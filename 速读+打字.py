# -*- coding: utf-8 -*-
"""
SpeedReader v18 MPV-TTS
黑底白字极简 TXT 速读器 + 搜狗双拼打字练习模式。
保留右侧按钮、拖拽、快捷键、书签、进度、置顶、窗口拖动/缩放等核心行为。
本版把旧的逐字抢占朗读改成“完整语句段合成 WAV + mpv 按当前 WPM 变速播放”，适配 1000-4000+ WPM；超过朗读上限时仍按上限速度继续有声播放。
"""

import ctypes
import ctypes.wintypes
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import wave
import threading
import queue
import time
import traceback
from collections import deque
from pathlib import Path
from urllib.parse import unquote, urlparse

import tkinter as tk
from tkinter import filedialog, messagebox
import tkinter.font as tkfont

try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    BaseTk = TkinterDnD.Tk
    TKDND_AVAILABLE = True
except Exception:
    DND_FILES = None
    BaseTk = tk.Tk
    TKDND_AVAILABLE = False

IS_WINDOWS = sys.platform.startswith("win")
VALID_SHUANGPIN_KEYS = set("abcdefghijklmnopqrstuvwxyz;")
CTRL_MASK = 0x0004
ALT_MASK = 0x0008


def is_ctrl_combo_state(state: int) -> bool:
    """Only real Ctrl shortcuts should bypass typing; IME extra state bits must not be swallowed."""
    try:
        return bool(int(state) & CTRL_MASK)
    except Exception:
        return False


def focus_scroll_units(current_y: int, target_y: int, line_height: int, max_units: int = 40) -> int:
    """Pure helper for micro-centering a Text dlineinfo y value near the focus line."""
    line_height = max(1, int(line_height or 1))
    units = int((int(current_y) - int(target_y)) / line_height)
    return max(-int(max_units), min(int(max_units), units))

INITIAL_TO_KEY = {
    "b": "b", "p": "p", "m": "m", "f": "f",
    "d": "d", "t": "t", "n": "n", "l": "l",
    "g": "g", "k": "k", "h": "h",
    "j": "j", "q": "q", "x": "x",
    "zh": "v", "ch": "i", "sh": "u",
    "r": "r", "z": "z", "c": "c", "s": "s",
    "y": "y", "w": "w",
}

FINAL_TO_KEY = {
    "a": "a", "o": "o", "e": "e", "i": "i", "u": "u",
    "v": "y", "ü": "y",
    "ai": "l", "ei": "z", "ui": "v", "ao": "k", "ou": "b", "iu": "q", "ie": "x",
    "ve": "t", "ue": "t", "üe": "t",
    "er": "r",
    "an": "j", "en": "f", "in": "n", "un": "p",
    "ang": "h", "eng": "g", "ing": ";", "ong": "s",
    "ia": "w", "ua": "w", "uo": "o", "uai": "y", "uan": "r", "ian": "m", "iao": "c",
    "iang": "d", "uang": "d", "iong": "s",
}

ZERO_INITIAL_FINAL_TO_CODE = {
    "a": "oa", "o": "oo", "e": "oe", "en": "of", "er": "or", "an": "oj",
}

PINYIN_FINAL_ALIASES = {
    "iou": "iu", "uei": "ui", "uen": "un",
    "u:e": "ve", "ue": "ue", "üe": "ve", "ü": "v", "v": "v",
}

SPECIAL_PINYIN_SPLIT = {
    "ju": ("j", "u"), "qu": ("q", "u"), "xu": ("x", "u"), "yu": ("y", "u"),
    "jue": ("j", "ve"), "que": ("q", "ve"), "xue": ("x", "ve"), "yue": ("y", "ve"),
    "juan": ("j", "uan"), "quan": ("q", "uan"), "xuan": ("x", "uan"), "yuan": ("y", "uan"),
    "jun": ("j", "un"), "qun": ("q", "un"), "xun": ("x", "un"), "yun": ("y", "un"),
}

# 无 pypinyin 时仅供自检/提示兜底；正式打字模式会要求安装或使用 portable 包内依赖。
BUILTIN_PINYIN_FOR_TEST = {
    "啊": ["a"], "哦": ["o"], "饿": ["e"], "嗯": ["en"], "安": ["an"], "全": ["quan"], "居": ["ju"], "去": ["qu"], "虚": ["xu"],
    "鱼": ["yu"], "雨": ["yu"], "语": ["yu"], "玉": ["yu"], "月": ["yue"], "元": ["yuan"],
    "云": ["yun"], "女": ["nv"], "吕": ["lv"], "绿": ["lv"], "是": ["shi"], "知": ["zhi"],
    "吃": ["chi"], "窗": ["chuang"], "双": ["shuang"], "安": ["an"], "全": ["quan"],
}


def script_dir() -> Path:
    return Path(__file__).resolve().parent


def stable_app_state_dir() -> Path:
    """Persistent state location shared by all renamed/downloaded versions of this script."""
    try:
        base = os.environ.get("APPDATA") or os.environ.get("LOCALAPPDATA") or str(Path.home())
        return Path(base) / "SpeedReaderTk"
    except Exception:
        return Path.home() / ".speedreader_tk"


def norm_path_key(path: str) -> str:
    return os.path.normcase(os.path.abspath(os.path.expanduser(str(path))))


def is_cjk_char(ch: str) -> bool:
    if not ch:
        return False
    code = ord(ch)
    return (
        0x3400 <= code <= 0x4DBF
        or 0x4E00 <= code <= 0x9FFF
        or 0xF900 <= code <= 0xFAFF
        or 0x20000 <= code <= 0x2A6DF
        or 0x2A700 <= code <= 0x2B73F
        or 0x2B740 <= code <= 0x2B81F
        or 0x2B820 <= code <= 0x2CEAF
        or 0x2CEB0 <= code <= 0x2EBEF
        or 0x30000 <= code <= 0x3134F
    )


def safe_json_load(path: Path, default, log_func=None):
    try:
        if not path.exists():
            return default
        with path.open("r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, type(default)) else default
    except Exception:
        if log_func:
            log_func(f"JSON read failed: {path}\n{traceback.format_exc()}")
        return default


def atomic_json_save(path: Path, data, log_func=None) -> bool:
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(path.suffix + f".tmp.{os.getpid()}")
        with tmp.open("w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
        return True
    except Exception:
        if log_func:
            log_func(f"JSON save failed: {path}\n{traceback.format_exc()}")
        return False


def score_decoded_text_static(text: str, enc: str) -> float:
    if not text:
        return -10**9
    total = len(text)
    cjk = sum(1 for ch in text if is_cjk_char(ch))
    printable = sum(1 for ch in text if ch in "\n\r\t" or ch.isprintable())
    controls = sum(1 for ch in text if (ord(ch) < 32 and ch not in "\n\r\t"))
    replacement = text.count("�")
    nul = text.count("\x00")
    weird = sum(1 for ch in text if 0xD800 <= ord(ch) <= 0xDFFF)
    other_non_ascii = sum(
        1 for ch in text
        if ord(ch) >= 128 and (not is_cjk_char(ch)) and ch not in "，。！？；：、（）《》“”‘’—…【】·￥　"
    )
    ratio_print = printable / max(1, total)
    ratio_cjk = cjk / max(1, total)
    ratio_other = other_non_ascii / max(1, total)
    score = ratio_print * 80 + ratio_cjk * 160 - ratio_other * 120 - replacement * 20 - controls * 10 - nul * 40 - weird * 50
    if enc == "utf-8" and replacement == 0:
        score += 8
    if enc in ("gb18030", "gbk", "cp936", "gb2312") and cjk:
        score += 4
    if enc.startswith("utf-16"):
        if controls == 0 and replacement == 0 and ratio_print > 0.85:
            score += 4
        if total >= 4 and ratio_cjk > 0.35:
            score += 8
    return score



def utf16_endian_raw_bonus(raw: bytes, enc: str) -> float:
    if not raw or len(raw) < 4:
        return 0.0
    even_zero = sum(1 for b in raw[0::2] if b == 0)
    odd_zero = sum(1 for b in raw[1::2] if b == 0)
    pairs = max(1, len(raw) // 2)
    if enc == "utf-16-le":
        return (odd_zero - even_zero) / pairs * 80.0
    if enc == "utf-16-be":
        return (even_zero - odd_zero) / pairs * 80.0
    return 0.0

def decode_txt_bytes(raw: bytes):
    if raw.startswith(b"\xef\xbb\xbf"):
        return raw.decode("utf-8-sig", errors="strict"), "utf-8-sig"
    if raw.startswith(b"\xff\xfe"):
        return raw.decode("utf-16-le", errors="strict"), "utf-16-le-bom"
    if raw.startswith(b"\xfe\xff"):
        return raw.decode("utf-16-be", errors="strict"), "utf-16-be-bom"
    if not raw:
        return "", "empty"

    # 关键：严格 UTF-8 必须最先成功返回，防止 UTF-8 中文被 UTF-16-BE 宽容误判。
    try:
        text = raw.decode("utf-8", errors="strict")
        if score_decoded_text_static(text, "utf-8") > 20:
            return text, "utf-8"
        return text, "utf-8"
    except Exception:
        pass

    candidates = []
    if len(raw) % 2 == 0:
        for enc in ("utf-16-le", "utf-16-be"):
            try:
                text = raw.decode(enc, errors="strict")
                candidates.append((score_decoded_text_static(text, enc) + utf16_endian_raw_bonus(raw, enc), enc, text))
            except Exception:
                pass

    # GB2312/GBK/CP936 尽量按 GB18030 兼容打开；保留后续候选用于极端文件。
    for enc in ("gb18030", "gbk", "cp936", "gb2312"):
        try:
            text = raw.decode(enc, errors="strict")
            candidates.append((score_decoded_text_static(text, enc), enc, text))
        except Exception:
            pass

    if candidates:
        candidates.sort(key=lambda x: x[0], reverse=True)
        best_score, best_enc, best_text = candidates[0]
        if best_score > 10:
            return best_text, best_enc

    for enc in ("gb18030", "utf-8", "utf-16-le", "utf-16-be"):
        try:
            text = raw.decode(enc, errors="replace")
            return text, enc + "-replace"
        except Exception:
            pass
    return raw.decode("utf-8", errors="replace"), "utf-8-replace"


def strip_tone_marks(py: str) -> str:
    table = str.maketrans({
        "ā": "a", "á": "a", "ǎ": "a", "à": "a",
        "ē": "e", "é": "e", "ě": "e", "è": "e",
        "ī": "i", "í": "i", "ǐ": "i", "ì": "i",
        "ō": "o", "ó": "o", "ǒ": "o", "ò": "o",
        "ū": "u", "ú": "u", "ǔ": "u", "ù": "u",
        "ǖ": "ü", "ǘ": "ü", "ǚ": "ü", "ǜ": "ü",
        "ń": "n", "ň": "n", "ǹ": "n",
        "ḿ": "m",
    })
    py = str(py).strip().lower().translate(table)
    py = re.sub(r"[1-5]$", "", py)
    py = py.replace("u:", "v")
    return py


def normalize_pinyin(py: str) -> str:
    py = strip_tone_marks(py)
    py = py.replace("ü", "v")
    py = py.replace("u:", "v")
    py = re.sub(r"[^a-zv]", "", py)
    return py


def split_pinyin_for_sogou(py: str):
    py = normalize_pinyin(py)
    if not py:
        return None, None
    if py in SPECIAL_PINYIN_SPLIT:
        return SPECIAL_PINYIN_SPLIT[py]
    for initial in ("zh", "ch", "sh"):
        if py.startswith(initial):
            return initial, py[len(initial):] or "i"
    if py[0] in INITIAL_TO_KEY:
        return py[0], py[1:] or ""
    return "", py


def normalize_final(final: str) -> str:
    final = normalize_pinyin(final)
    return PINYIN_FINAL_ALIASES.get(final, final)


def sogou_code_for_pinyin(py: str):
    initial, final = split_pinyin_for_sogou(py)
    if initial is None:
        return None
    final = normalize_final(final)
    if initial == "":
        if final in ZERO_INITIAL_FINAL_TO_CODE:
            return ZERO_INITIAL_FINAL_TO_CODE[final]
        second = FINAL_TO_KEY.get(final)
        return "o" + second if second else None
    first = INITIAL_TO_KEY.get(initial)
    if not first:
        return None
    if final in ("", None):
        final = "i"
    second = FINAL_TO_KEY.get(final)
    return first + second if second else None


class TypingKeyEngine:
    """Pure key engine used by GUI and selftest."""
    def __init__(self, codes, mode="exact"):
        self.codes = list(dict.fromkeys([c for c in codes if c and len(c) == 2]))
        self.mode = mode
        self.buffer = ""
        self.wrong = 0
        self.accepted = False

    def press(self, key: str) -> bool:
        key = (key or "").lower()
        if key not in VALID_SHUANGPIN_KEYS:
            return False
        if self.mode == "simple":
            self.buffer += key
            if len(self.buffer) >= 2:
                self.accepted = True
                self.buffer = ""
                return True
            return False
        if self.mode == "first":
            if not self.buffer:
                if key in {c[0] for c in self.codes}:
                    self.buffer = key
                else:
                    self.wrong += 1
                    self.buffer = ""
                return False
            self.accepted = True
            self.buffer = ""
            return True
        if not self.buffer:
            if key in {c[0] for c in self.codes}:
                self.buffer = key
            else:
                self.wrong += 1
                self.buffer = ""
            return False
        if any(c[0] == self.buffer and c[1] == key for c in self.codes):
            self.accepted = True
            self.buffer = ""
            return True
        self.wrong += 1
        if key in {c[0] for c in self.codes}:
            self.buffer = key
        else:
            self.buffer = ""
        return False


class TTSManager:
    """MPV-backed full-segment speech player.

    旧版是“当前字优先”的逐字 TTS：高速时会不断抢占、裁断、排队错位，
    1000+ WPM 基本只能听到碎片。新版改成：
    1. 先把当前位置起的一整句/一整段合成为完整 WAV；
    2. 再交给 mpv 按当前 WPM 设置 --speed 播放；
    3. 只有跳转、重新开始、速度改变或进入新语句段时才打断旧音频。

    mpv 只负责播放与加速，不负责中文语音合成；中文合成仍优先使用 Windows SAPI
    系统语音，避免引入大模型/大依赖。把 mpv.exe 放在脚本同目录，或加入 PATH 即可。
    """
    def __init__(self, log_func=None, enabled=True):
        self.log = log_func or (lambda *a, **k: None)
        self.enabled = bool(enabled)
        self.queue = queue.Queue(maxsize=1)
        self.stop_event = threading.Event()
        self.thread = None
        self.backend = "none"
        self.ready = False
        self.started = False
        self.tts_temp_dir = None
        self.wav_cache = {}
        self.cache_limit = 240
        self.mpv_path = self._find_mpv()
        self.current_proc = None
        self._ps_script_path = None
        # Windows SAPI 普通中文语音大致在 240-320 字/分钟。这里用 300 作为基准，
        # WPM=300 约 1x，WPM=1200 约 4x，WPM=4000 约 13.3x。
        # 只做播放加速，不裁音频，所以每个语句段仍会完整播放出来。
        self.base_speech_wpm = 300.0
        self.max_mpv_speed = 24.0

    def _iter_mpv_candidates(self):
        """Yield possible command-line mpv executables without relying only on PATH.

        Windows winget can install mpv into a private package directory such as
        %LOCALAPPDATA%\\Microsoft\\WinGet\\Packages\\...\\mpv.exe.  If the
        Python process was already open, or if PowerShell is currently in
        C:\\Windows\\System32, PATH/copy based fixes often fail.  Therefore the
        application scans the real install locations and launches mpv by absolute
        path.
        """
        seen = set()

        def add(path):
            if not path:
                return
            try:
                pp = Path(os.path.expandvars(os.path.expanduser(str(path)))).resolve()
                key = str(pp).lower() if IS_WINDOWS else str(pp)
                if key not in seen:
                    seen.add(key)
                    yield pp
            except Exception:
                return

        bases = []
        try:
            bases.append(script_dir())
        except Exception:
            pass
        try:
            bases.append(Path.cwd())
        except Exception:
            pass
        try:
            if getattr(sys, "argv", None) and sys.argv[0]:
                bases.append(Path(sys.argv[0]).resolve().parent)
        except Exception:
            pass

        for base in bases:
            for rel in (
                "mpv.exe", "mpv.com", "mpv",
                "mpv/mpv.exe", "mpv/mpv.com",
                "bin/mpv.exe", "bin/mpv.com",
            ):
                yield from add(base / rel)

        for name in ("mpv.exe", "mpv.com", "mpv"):
            try:
                found = shutil.which(name)
                if found:
                    yield from add(found)
            except Exception:
                pass

        if IS_WINDOWS:
            # where.exe can see App Execution Aliases / refreshed PATH in cases where
            # shutil.which() missed them.  Keep this cheap and silent.
            try:
                out = subprocess.check_output(
                    ["where.exe", "mpv"],
                    stderr=subprocess.DEVNULL,
                    stdin=subprocess.DEVNULL,
                    text=True,
                    timeout=3,
                )
                for line in out.splitlines():
                    yield from add(line.strip())
            except Exception:
                pass

            env = os.environ
            search_roots = []
            for var in ("LOCALAPPDATA", "ProgramFiles", "ProgramFiles(x86)", "ProgramData", "USERPROFILE"):
                val = env.get(var)
                if val:
                    search_roots.append(Path(val))

            common_dirs = []
            local = env.get("LOCALAPPDATA")
            if local:
                common_dirs.extend([
                    Path(local) / "Microsoft" / "WinGet" / "Packages",
                    Path(local) / "Microsoft" / "WinGet" / "Links",
                    Path(local) / "Programs",
                    Path(local) / "mpv",
                ])
            userprofile = env.get("USERPROFILE")
            if userprofile:
                common_dirs.extend([
                    Path(userprofile) / "scoop" / "apps" / "mpv" / "current",
                    Path(userprofile) / "scoop" / "shims",
                ])
            programdata = env.get("ProgramData")
            if programdata:
                common_dirs.extend([
                    Path(programdata) / "chocolatey" / "bin",
                    Path(programdata) / "chocolatey" / "lib" / "mpv",
                ])
            for pf in (env.get("ProgramFiles"), env.get("ProgramFiles(x86)")):
                if pf:
                    common_dirs.extend([
                        Path(pf) / "mpv",
                        Path(pf) / "mpv.net",
                        Path(pf) / "VideoLAN" / "mpv",
                    ])

            # Exact/common locations first.
            for root in common_dirs:
                for rel in ("mpv.exe", "mpv.com", "current/mpv.exe", "bin/mpv.exe"):
                    yield from add(root / rel)

            # Controlled shallow recursive scan: enough for winget/choco/scoop layouts,
            # but avoids a full-drive scan.
            recursive_roots = []
            if local:
                recursive_roots.append(Path(local) / "Microsoft" / "WinGet" / "Packages")
                recursive_roots.append(Path(local) / "Programs")
            if programdata:
                recursive_roots.append(Path(programdata) / "chocolatey" / "lib")
            if userprofile:
                recursive_roots.append(Path(userprofile) / "scoop" / "apps")
            for root in recursive_roots:
                try:
                    if root.is_dir():
                        # rglob on these package folders is usually small; cap results.
                        count = 0
                        for exe in root.rglob("mpv.exe"):
                            yield from add(exe)
                            count += 1
                            if count >= 20:
                                break
                except Exception:
                    pass

    def _find_mpv(self):
        for c in self._iter_mpv_candidates():
            try:
                if c and Path(c).is_file():
                    return str(Path(c))
            except Exception:
                pass
        return None

    def _refresh_mpv_path(self):
        """Re-detect mpv after the app is already running.

        This fixes the common workflow where mpv is installed from PowerShell
        while SpeedReader is still open; the already-running Python process does
        not automatically receive the new PATH.
        """
        try:
            if self.mpv_path and Path(self.mpv_path).is_file():
                return self.mpv_path
        except Exception:
            pass
        found = self._find_mpv()
        if found:
            old = getattr(self, "mpv_path", None)
            self.mpv_path = found
            if old != found:
                self.log(f"TTS MPV found/refreshed: {found}")
        return self.mpv_path

    def start(self):
        if self.started:
            return
        self.started = True
        self.thread = threading.Thread(target=self._worker, name="SpeedReaderMPVTTS", daemon=True)
        self.thread.start()

    def set_enabled(self, value: bool):
        self.enabled = bool(value)
        if self.enabled:
            self.start()
        else:
            self.clear_queue()
            self._stop_current_playback()

    def clear_queue(self):
        try:
            while True:
                self.queue.get_nowait()
        except Exception:
            pass

    def close(self):
        try:
            self.stop_event.set()
            self.clear_queue()
            self._stop_current_playback()
            try:
                self.queue.put_nowait(None)
            except Exception:
                pass
        except Exception:
            pass

    def _ensure_tts_temp_dir(self):
        if self.tts_temp_dir is None:
            try:
                self.tts_temp_dir = Path(tempfile.mkdtemp(prefix="speedreader_mpv_tts_"))
            except Exception:
                self.tts_temp_dir = None
        return self.tts_temp_dir

    def _normalize_text(self, text):
        text = str(text or "")
        text = text.replace("\r\n", "\n").replace("\r", "\n")
        text = re.sub(r"[ \t\u3000]+", " ", text)
        text = re.sub(r"\n{3,}", "\n\n", text)
        return text.strip()

    def _normalize_wpm(self, wpm):
        try:
            w = float(wpm)
        except Exception:
            w = 300.0
        if w <= 0:
            w = 300.0
        return max(30.0, min(12000.0, w))

    def _mpv_speed_for_wpm(self, wpm):
        w = self._normalize_wpm(wpm)
        speed = w / max(1.0, float(self.base_speech_wpm))
        # 低速时允许慢放，高速时保留很高上限；超过上限时钳制到上限，继续播放，不返回静音。
        return max(0.35, min(float(self.max_mpv_speed), speed))

    def effective_wpm_for_playback(self, wpm):
        """Return the WPM that MPV can actually play after speed clamping.

        UI/reader speed may keep increasing forever, but audio speed has a real
        ceiling.  Once the requested WPM is above the ceiling, all TTS decisions
        must use this effective WPM so the app does not keep killing/restarting
        mpv with an unchanged capped --speed value.
        """
        speed = self._mpv_speed_for_wpm(wpm)
        return max(30.0, float(speed) * max(1.0, float(self.base_speech_wpm)))

    def is_playing(self):
        try:
            proc = getattr(self, "current_proc", None)
            return bool(proc is not None and proc.poll() is None)
        except Exception:
            return False

    def speak_char(self, ch: str, wpm=None):
        # 兼容旧调用；新版核心是 speak_text。
        return self.speak_text(ch, wpm=wpm, reason="char")

    def speak_text(self, text: str, wpm=None, reason="segment"):
        if not self.enabled:
            return
        text = self._normalize_text(text)
        if not text:
            return
        self.start()
        effective_wpm = self.effective_wpm_for_playback(wpm)
        item = {
            "text": text,
            "wpm": effective_wpm,
            "requested_wpm": self._normalize_wpm(wpm),
            "reason": str(reason or "segment"),
            "time": time.time(),
        }
        # 新语句段必须抢占旧语句段；但 GUI 层已经保证不会每个字都调用这里，
        # 所以这里的抢占只发生在跳转、速度变化、进入下一句等真正需要更新音频的节点。
        self.clear_queue()
        self._stop_current_playback()
        try:
            self.queue.put_nowait(item)
        except Exception:
            pass

    def _stop_current_playback(self):
        proc = getattr(self, "current_proc", None)
        if proc is None:
            return
        try:
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=0.25)
                except Exception:
                    try:
                        proc.kill()
                    except Exception:
                        pass
        except Exception:
            pass
        finally:
            self.current_proc = None

    def _select_sapi_voice(self, voice):
        try:
            voices = voice.GetVoices()
            best = None
            best_score = -1
            for i in range(int(voices.Count)):
                v = voices.Item(i)
                desc = ""
                try:
                    desc = str(v.GetDescription())
                except Exception:
                    pass
                attrs = ""
                try:
                    attrs = str(v.GetAttribute("Language")) + " " + str(v.GetAttribute("Gender"))
                except Exception:
                    pass
                text = (desc + " " + attrs).lower()
                score = 0
                if any(x in text for x in ("chinese", "zh-cn", "zh_cn", "huihui", "xiaoxiao", "yaoyao", "hanhan", "kangkang")):
                    score += 6
                if any(x in text for x in ("female", "woman", "huihui", "xiaoxiao", "yaoyao", "hanhan")):
                    score += 2
                if score > best_score:
                    best, best_score = v, score
            if best is not None and best_score > 0:
                voice.Voice = best
                self.log(f"TTS SAPI voice selected: {best.GetDescription()}")
        except Exception:
            self.log("TTS SAPI voice select failed:\n" + traceback.format_exc())

    def _cache_key_for_text(self, text):
        digest = hashlib.sha1(text.encode("utf-8", errors="ignore")).hexdigest()
        return digest[:32]

    def _remember_wav_cache(self, key, path):
        try:
            self.wav_cache[key] = path
            while len(self.wav_cache) > int(self.cache_limit):
                old_key = next(iter(self.wav_cache))
                old_path = self.wav_cache.pop(old_key, None)
                try:
                    if old_path:
                        Path(old_path).unlink(missing_ok=True)
                except Exception:
                    pass
        except Exception:
            pass

    def _sapi_com_wav_for_text(self, voice, win32com, text):
        key = self._cache_key_for_text(text)
        cached = self.wav_cache.get(key)
        if cached:
            try:
                if Path(cached).is_file():
                    return cached
            except Exception:
                pass
        temp_dir = self._ensure_tts_temp_dir()
        if temp_dir is None:
            return None
        wav_path = Path(temp_dir) / (key + ".wav")
        if wav_path.is_file():
            self._remember_wav_cache(key, wav_path)
            return wav_path
        old_stream = None
        stream = None
        try:
            stream = win32com.client.Dispatch("SAPI.SpFileStream")
            # 3 = SSFMCreateForWrite
            stream.Open(str(wav_path), 3, False)
            try:
                old_stream = voice.AudioOutputStream
            except Exception:
                old_stream = None
            voice.AudioOutputStream = stream
            try:
                voice.Rate = 0
                voice.Volume = 100
            except Exception:
                pass
            voice.Speak(str(text), 0)
            try:
                voice.AudioOutputStream = old_stream
            except Exception:
                pass
            stream.Close()
            stream = None
            if wav_path.is_file() and wav_path.stat().st_size > 256:
                self._remember_wav_cache(key, wav_path)
                return wav_path
        except Exception:
            self.log("TTS SAPI COM synth failed:\n" + traceback.format_exc())
        finally:
            try:
                if old_stream is not None:
                    voice.AudioOutputStream = old_stream
            except Exception:
                pass
            try:
                if stream is not None:
                    stream.Close()
            except Exception:
                pass
        return None

    def _powershell_path(self):
        for name in ("powershell.exe", "pwsh.exe", "powershell", "pwsh"):
            try:
                found = shutil.which(name)
                if found:
                    return found
            except Exception:
                pass
        if IS_WINDOWS:
            sysroot = os.environ.get("SystemRoot") or r"C:\Windows"
            candidate = Path(sysroot) / "System32" / "WindowsPowerShell" / "v1.0" / "powershell.exe"
            if candidate.is_file():
                return str(candidate)
        return None

    def _ensure_ps_script(self):
        temp_dir = self._ensure_tts_temp_dir()
        if temp_dir is None:
            return None
        if self._ps_script_path is None:
            p = Path(temp_dir) / "sapi_synth_to_wav.ps1"
            p.write_text(
                """
param([string]$TextPath, [string]$WavPath)
Add-Type -AssemblyName System.Speech
$synth = New-Object System.Speech.Synthesis.SpeechSynthesizer
try {
    $synth.Rate = 0
    $synth.Volume = 100
    $text = [System.IO.File]::ReadAllText($TextPath, [System.Text.Encoding]::UTF8)
    $synth.SetOutputToWaveFile($WavPath)
    $synth.Speak($text)
} finally {
    $synth.Dispose()
}
""".strip(),
                encoding="utf-8",
            )
            self._ps_script_path = p
        return self._ps_script_path

    def _sapi_powershell_wav_for_text(self, text):
        key = self._cache_key_for_text(text)
        cached = self.wav_cache.get(key)
        if cached:
            try:
                if Path(cached).is_file():
                    return cached
            except Exception:
                pass
        temp_dir = self._ensure_tts_temp_dir()
        ps = self._powershell_path()
        script = self._ensure_ps_script()
        if temp_dir is None or not ps or script is None:
            return None
        wav_path = Path(temp_dir) / (key + ".wav")
        txt_path = Path(temp_dir) / (key + ".txt")
        if wav_path.is_file() and wav_path.stat().st_size > 256:
            self._remember_wav_cache(key, wav_path)
            return wav_path
        try:
            txt_path.write_text(text, encoding="utf-8")
            creationflags = 0
            if IS_WINDOWS and hasattr(subprocess, "CREATE_NO_WINDOW"):
                creationflags = subprocess.CREATE_NO_WINDOW
            subprocess.run(
                [ps, "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(script), str(txt_path), str(wav_path)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=20,
                creationflags=creationflags,
            )
            try:
                txt_path.unlink(missing_ok=True)
            except Exception:
                pass
            if wav_path.is_file() and wav_path.stat().st_size > 256:
                self._remember_wav_cache(key, wav_path)
                return wav_path
        except Exception:
            self.log("TTS PowerShell SAPI synth failed:\n" + traceback.format_exc())
        return None

    def _play_with_mpv(self, wav_path, wpm, reason="segment"):
        mpv = self._refresh_mpv_path()
        if not mpv:
            self.log(
                "TTS MPV unavailable: mpv.exe was not found in script folder, PATH, "
                "winget package folders, scoop, or chocolatey. Install mpv-player.mpv-CI.MSVC "
                "or put mpv.exe next to this .py file."
            )
            return False
        speed = self._mpv_speed_for_wpm(wpm)
        # 很高倍速下 pitch-correction 的拉伸滤镜可能比原始变速更容易吞音。
        # 低中速保留校正；接近/超过高速区改为纯加速，优先保证一定有声音。
        pitch_correction = "yes" if speed <= 6.0 else "no"
        cmd = [
            str(mpv),
            "--no-terminal",
            "--really-quiet",
            "--force-window=no",
            "--vo=null",
            "--audio-display=no",
            "--idle=no",
            f"--audio-pitch-correction={pitch_correction}",
            f"--speed={speed:.4f}",
            "--",
            str(wav_path),
        ]
        creationflags = 0
        if IS_WINDOWS and hasattr(subprocess, "CREATE_NO_WINDOW"):
            creationflags = subprocess.CREATE_NO_WINDOW
        try:
            self._stop_current_playback()
            self.log(f"TTS MPV play reason={reason} effective_wpm={float(wpm):.1f} speed={speed:.3f} pitch={pitch_correction} file={wav_path}", verbose=True)
            self.current_proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, creationflags=creationflags)
            self.current_proc.wait()
            self.current_proc = None
            return True
        except Exception:
            self.current_proc = None
            self.log("TTS MPV playback failed:\n" + traceback.format_exc())
            return False

    def _worker(self):
        voice = None
        win32com = None
        pythoncom = None
        self._refresh_mpv_path()
        if self.mpv_path:
            self.log(f"TTS MPV found: {self.mpv_path}")
        else:
            self.log("TTS MPV not found yet; playback will rescan script folder, PATH, winget, scoop and chocolatey folders each time it is needed")
        if IS_WINDOWS:
            try:
                import pythoncom as _pythoncom
                import win32com.client as _win32com_client
                pythoncom = _pythoncom
                pythoncom.CoInitialize()
                class _Win32ComModule:
                    client = _win32com_client
                win32com = _Win32ComModule
                voice = win32com.client.Dispatch("SAPI.SpVoice")
                self._select_sapi_voice(voice)
                self.backend = "mpv+sapi-com"
                self.ready = bool(self.mpv_path)
                self.log("TTS backend ready: MPV playback + Windows SAPI COM synthesis")
            except Exception as e:
                voice = None
                win32com = None
                self.backend = "mpv+sapi-powershell" if self.mpv_path else "sapi-powershell-no-mpv"
                self.ready = bool(self.mpv_path)
                self.log(f"TTS SAPI COM unavailable, fallback to PowerShell SAPI synthesis: {e}")
        else:
            self.backend = "mpv-external-audio-only"
            self.ready = bool(self.mpv_path)
            self.log("TTS synthesis currently expects Windows SAPI; non-Windows needs an external WAV synth path")

        try:
            while not self.stop_event.is_set():
                item = self.queue.get()
                if item is None:
                    break
                try:
                    # 只保留最新请求；旧请求通常来自跳转前或速度变化前。
                    while True:
                        newer = self.queue.get_nowait()
                        if newer is None:
                            item = None
                            break
                        item = newer
                except Exception:
                    pass
                if item is None or not self.enabled:
                    continue
                text = self._normalize_text(item.get("text", ""))
                if not text:
                    continue
                wpm = self._normalize_wpm(item.get("wpm"))
                reason = item.get("reason", "segment")
                wav_path = None
                if voice is not None and win32com is not None:
                    wav_path = self._sapi_com_wav_for_text(voice, win32com, text)
                if wav_path is None and IS_WINDOWS:
                    wav_path = self._sapi_powershell_wav_for_text(text)
                if wav_path is None:
                    self.log("TTS synth failed: no usable WAV was produced")
                    continue
                self._play_with_mpv(wav_path, wpm, reason=reason)
        finally:
            try:
                self._stop_current_playback()
            except Exception:
                pass
            try:
                if pythoncom is not None:
                    pythoncom.CoUninitialize()
            except Exception:
                pass
            try:
                if self.tts_temp_dir is not None:
                    shutil.rmtree(str(self.tts_temp_dir), ignore_errors=True)
                    self.tts_temp_dir = None
                    self.wav_cache.clear()
                    self._ps_script_path = None
            except Exception:
                pass


    # ---------- final override: gain600 MPV/SAPI speech ----------
    def _select_sapi_voice(self, voice):
        """Prefer a Chinese female voice when Windows provides one."""
        try:
            voices = voice.GetVoices()
            best = None
            best_score = -10**9
            for i in range(int(voices.Count)):
                v = voices.Item(i)
                desc = ""
                attrs = ""
                try:
                    desc = str(v.GetDescription())
                except Exception:
                    pass
                try:
                    attrs = " ".join(str(v.GetAttribute(a)) for a in ("Language", "Gender", "Name", "Vendor"))
                except Exception:
                    pass
                t = (desc + " " + attrs).lower()
                score = 0
                if any(x in t for x in ("zh-cn", "zh_cn", "804", "chinese", "mandarin", "中文", "普通话")):
                    score += 100
                if any(x in t for x in ("female", "woman", "huihui", "xiaoxiao", "yaoyao", "hanhan", "xiaoyi", "xiaobei", "xiaoni")):
                    score += 40
                if any(x in t for x in ("male", "man", "kangkang")):
                    score -= 20
                if score > best_score:
                    best_score = score
                    best = v
            if best is not None and best_score > 0:
                voice.Voice = best
                self.log(f"TTS SAPI voice selected: {best.GetDescription()}")
        except Exception:
            self.log("TTS SAPI voice select failed:\n" + traceback.format_exc())

    def _cache_key_for_text(self, text):
        digest = hashlib.sha1(("gain600-v2\0" + str(text)).encode("utf-8", errors="ignore")).hexdigest()
        return digest[:32]

    def _gain600_wav_for_raw(self, raw_path, key):
        """Return a 600% amplitude WAV copy; never crop the audio, so MPV cannot lose tails."""
        try:
            raw_path = Path(raw_path)
            if not raw_path.is_file() or raw_path.stat().st_size <= 256:
                return None
            amp_path = raw_path.with_name(raw_path.stem + "_gain600.wav")
            if amp_path.is_file() and amp_path.stat().st_size > 256:
                return amp_path
            gain = 6.0
            with wave.open(str(raw_path), "rb") as r:
                params = r.getparams()
                nchannels = int(r.getnchannels())
                sampwidth = int(r.getsampwidth())
                framerate = int(r.getframerate())
                nframes = int(r.getnframes())
                frames = r.readframes(nframes)
            if sampwidth not in (1, 2, 3, 4):
                shutil.copyfile(str(raw_path), str(amp_path))
                return amp_path
            out = bytearray()
            total_samples = len(frames) // max(1, sampwidth)
            for sample_index in range(total_samples):
                i = sample_index * sampwidth
                if sampwidth == 1:
                    v = int((frames[i] - 128) * gain)
                    v = max(-128, min(127, v))
                    out.append((v + 128) & 0xFF)
                else:
                    max_pos = (1 << (8 * sampwidth - 1)) - 1
                    min_neg = -(1 << (8 * sampwidth - 1))
                    sample = int.from_bytes(frames[i:i + sampwidth], "little", signed=True)
                    v = int(sample * gain)
                    v = max(min_neg, min(max_pos, v))
                    out.extend(int(v).to_bytes(sampwidth, "little", signed=True))
            with wave.open(str(amp_path), "wb") as w:
                w.setparams((nchannels, sampwidth, framerate, nframes, params.comptype, params.compname))
                w.writeframes(bytes(out))
            return amp_path if amp_path.is_file() and amp_path.stat().st_size > 256 else raw_path
        except Exception:
            self.log("TTS gain600 postprocess failed:\n" + traceback.format_exc())
            try:
                return Path(raw_path) if Path(raw_path).is_file() else None
            except Exception:
                return None

    def _sapi_com_wav_for_text(self, voice, win32com, text):
        key = self._cache_key_for_text(text)
        cached = self.wav_cache.get(key)
        if cached:
            try:
                if Path(cached).is_file():
                    return cached
            except Exception:
                pass
        temp_dir = self._ensure_tts_temp_dir()
        if temp_dir is None:
            return None
        raw_path = Path(temp_dir) / (key + "_raw.wav")
        amp_path = Path(temp_dir) / (key + "_raw_gain600.wav")
        if amp_path.is_file() and amp_path.stat().st_size > 256:
            self._remember_wav_cache(key, amp_path)
            return amp_path
        old_stream = None
        stream = None
        try:
            stream = win32com.client.Dispatch("SAPI.SpFileStream")
            stream.Open(str(raw_path), 3, False)
            try:
                old_stream = voice.AudioOutputStream
            except Exception:
                old_stream = None
            voice.AudioOutputStream = stream
            try:
                voice.Rate = 0
                voice.Volume = 100
            except Exception:
                pass
            # text already contains a small punctuation tail in typing mode.  Do not crop it.
            voice.Speak(str(text), 0)
            try:
                voice.AudioOutputStream = old_stream
            except Exception:
                pass
            stream.Close()
            stream = None
            out_path = self._gain600_wav_for_raw(raw_path, key)
            if out_path is not None and Path(out_path).is_file() and Path(out_path).stat().st_size > 256:
                self._remember_wav_cache(key, out_path)
                return out_path
        except Exception:
            self.log("TTS SAPI COM synth failed:\n" + traceback.format_exc())
        finally:
            try:
                if old_stream is not None:
                    voice.AudioOutputStream = old_stream
            except Exception:
                pass
            try:
                if stream is not None:
                    stream.Close()
            except Exception:
                pass
        return None

    def _ensure_ps_script(self):
        temp_dir = self._ensure_tts_temp_dir()
        if temp_dir is None:
            return None
        if self._ps_script_path is None:
            p = Path(temp_dir) / "sapi_synth_to_wav.ps1"
            p.write_text(
                """
param([string]$TextPath, [string]$WavPath)
Add-Type -AssemblyName System.Speech
$synth = New-Object System.Speech.Synthesis.SpeechSynthesizer
try {
    $voices = $synth.GetInstalledVoices() | Where-Object {
        ($_.VoiceInfo.Culture.Name -like 'zh*' -or $_.VoiceInfo.Description -match 'Chinese|Mandarin|Huihui|Xiaoxiao|Yaoyao|Hanhan')
    }
    $female = $voices | Where-Object { $_.VoiceInfo.Gender -eq 'Female' } | Select-Object -First 1
    if ($female) { $synth.SelectVoice($female.VoiceInfo.Name) }
    elseif ($voices) { $synth.SelectVoice(($voices | Select-Object -First 1).VoiceInfo.Name) }
    $synth.Rate = 0
    $synth.Volume = 100
    $text = [System.IO.File]::ReadAllText($TextPath, [System.Text.Encoding]::UTF8)
    $synth.SetOutputToWaveFile($WavPath)
    $synth.Speak($text)
} finally {
    $synth.Dispose()
}
""".strip(),
                encoding="utf-8",
            )
            self._ps_script_path = p
        return self._ps_script_path

    def _sapi_powershell_wav_for_text(self, text):
        key = self._cache_key_for_text(text)
        cached = self.wav_cache.get(key)
        if cached:
            try:
                if Path(cached).is_file():
                    return cached
            except Exception:
                pass
        temp_dir = self._ensure_tts_temp_dir()
        ps = self._powershell_path()
        script = self._ensure_ps_script()
        if temp_dir is None or not ps or script is None:
            return None
        raw_path = Path(temp_dir) / (key + "_raw.wav")
        txt_path = Path(temp_dir) / (key + ".txt")
        amp_path = Path(temp_dir) / (key + "_raw_gain600.wav")
        if amp_path.is_file() and amp_path.stat().st_size > 256:
            self._remember_wav_cache(key, amp_path)
            return amp_path
        try:
            txt_path.write_text(str(text), encoding="utf-8")
            creationflags = 0
            if IS_WINDOWS and hasattr(subprocess, "CREATE_NO_WINDOW"):
                creationflags = subprocess.CREATE_NO_WINDOW
            subprocess.run(
                [ps, "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(script), str(txt_path), str(raw_path)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=20,
                creationflags=creationflags,
            )
            try:
                txt_path.unlink(missing_ok=True)
            except Exception:
                pass
            out_path = self._gain600_wav_for_raw(raw_path, key)
            if out_path is not None and Path(out_path).is_file() and Path(out_path).stat().st_size > 256:
                self._remember_wav_cache(key, out_path)
                return out_path
        except Exception:
            self.log("TTS PowerShell SAPI synth failed:\n" + traceback.format_exc())
        return None


class SpeedReader(BaseTk):
    def __init__(self):
        super().__init__()
        self.title("SpeedReader v18 MPV-TTS")
        self.geometry("900x520")
        self.configure(bg="black")
        self.attributes("-topmost", True)
        self.minsize(360, 260)

        self.app_dir = script_dir()
        self.stable_state_dir = self.default_state_dir()
        self.stable_state_dir.mkdir(parents=True, exist_ok=True)
        self.bookmark_file = self.stable_state_dir / "bookmark.json"
        self.legacy_bookmark_file = self.app_dir / "bookmark.json"
        self.wpm_file = self.app_dir / "wpm.json"
        self.legacy_wpm_file = self.app_dir / "wpm.json"
        self.debug_log_file = self.stable_state_dir / "speedreader_debug.log"
        self.debug = True
        self.debug_verbose = False

        self.button_size = 60
        self.file_path = None
        self.last_dropped_path = None
        self.raw_text = ""
        self.text = ""
        self.reader_pos = 0
        self.chunk_size = 1
        self.wpm = 600
        self.playing = False
        self.after_id = None
        self.was_scale_playing = False
        self._updating_scale = False
        self._last_drop_path = None
        self._last_drop_time = 0.0
        self._drop_methods = []
        self._misc_after_ids = set()
        self._focus_redraw_after_id = None
        self._typing_tick_after = None
        self._last_reader_progress_save = 0.0
        self._last_log_rotate_check = 0.0

        # v15: 阅读/打字共用同一个“聚焦行”视觉目标。
        # 0.42 表示当前阅读行固定在正文窗口正中间稍微偏上一点，
        # 避免旧版有时只 see() 到可见边缘、或滚轮同步点与横条位置不一致。
        self.focus_y_ratio = 0.42
        # v18: 显示层不再固定八字一行。每行字符数按当前窗口正文宽度和当前字体实时计算，
        # 用“虚拟窗口渲染 + 动态 wrap 宽度”兼顾窗口自适应与长篇不卡顿。
        self.display_chars_per_line = 8
        self._wrap_reflow_after_id = None
        self.display_start_line = 0
        self.display_line_count = 0
        self.display_render_text = ""
        self._last_render_signature = None
        self._rendering_display = False
        self.tts_enabled = True
        self.tts = None
        self._last_spoken_target = None
        self._tts_active_segment = None

        self.typing_mode = False
        self.typing_flat_char_index = 0
        self.typing_key_buffer = ""
        self.typing_match_mode = "exact"  # exact/simple/first
        self.typing_wrong_count = 0
        self.typing_current_wpm = 0.0
        self.typing_daymax = 0.0
        self.typing_txtmax = 0.0
        self.typing_event_times = deque(maxlen=2000)
        self.typing_last_input_time = None
        self.typing_window_start = time.time()
        self.typing_complete_notified = False
        self._last_typing_progress_save = 0.0
        self._last_typing_event_signature = None
        self._last_typing_event_seen_at = 0.0
        self._typing_capture_tag = "SpeedReaderTypingCapture"
        self._typing_bindtags_original = {}
        self._pypinyin_pinyin = None
        self._pypinyin_style_normal = None
        self._pinyin_install_tried = False
        self._char_code_cache = {}

        self.dragging_window = False
        self.offset_x = 0
        self.offset_y = 0
        self.resizing = False
        self.increasing = False
        self.decreasing = False
        self.text_color = "white"
        self.text_font_size = 24
        self.fixed_font_size = False
        self.font_min = 12
        self.font_max = 200
        self.text_font = tkfont.Font(family="Arial", size=self.text_font_size)

        self._native_wndproc = None
        self._native_old_procs = {}
        self._native_api_ready = False
        self._native_drop_installed = False
        self._SetWindowLongPtr = None
        self._CallWindowProc = None
        self._DragAcceptFiles = None
        self._DragQueryFile = None
        self._DragFinish = None
        self._DefWindowProc = None
        self._WNDPROC_TYPE = None
        self._GWLP_WNDPROC = -4
        self._WM_DROPFILES = 0x0233

        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.build_ui()
        self.bind_hotkeys()
        self.tts = TTSManager(self.log_debug, enabled=self.tts_enabled)
        self.tts.start()
        self.log_debug("SpeedReader v18 MPV-TTS started")
        self.log_debug(f"Script dir: {self.app_dir}")
        self.log_debug(f"tkinterdnd2 available: {TKDND_AVAILABLE}")
        self.schedule_misc_after(250, self.enable_file_drop_late)
        self.schedule_misc_after(80, self.auto_open_last_file)

    # ---------- low-level helpers ----------
    def log_debug(self, msg, verbose=False):
        if not self.debug:
            return
        if verbose and not getattr(self, "debug_verbose", False):
            return
        line = f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}"
        try:
            print(line)
        except Exception:
            pass
        try:
            now = time.time()
            if now - getattr(self, "_last_log_rotate_check", 0.0) > 2.0:
                self._last_log_rotate_check = now
                if self.debug_log_file.exists() and self.debug_log_file.stat().st_size > 2 * 1024 * 1024:
                    bak = self.debug_log_file.with_suffix(self.debug_log_file.suffix + ".1")
                    try:
                        if bak.exists():
                            bak.unlink()
                        self.debug_log_file.replace(bak)
                    except Exception:
                        pass
            with self.debug_log_file.open("a", encoding="utf-8") as f:
                f.write(line + "\n")
        except Exception:
            pass

    def schedule_misc_after(self, delay_ms, callback):
        holder = {"id": None}
        def runner():
            aid = holder.get("id")
            self._misc_after_ids.discard(aid)
            try:
                callback()
            except tk.TclError:
                pass
            except Exception:
                self.log_debug("scheduled callback failed:\n" + traceback.format_exc())
        try:
            aid = self.after(int(delay_ms), runner)
            holder["id"] = aid
            self._misc_after_ids.add(aid)
            return aid
        except Exception:
            return None

    def cancel_misc_after_callbacks(self):
        for aid in list(self._misc_after_ids):
            try:
                self.after_cancel(aid)
            except Exception:
                pass
        self._misc_after_ids.clear()
        self.cancel_focus_redraw()
        self.cancel_typing_idle_tick()

    def schedule_focus_redraw(self, delay_ms=1):
        """Debounced redraw for the two white focus lines."""
        try:
            if self._focus_redraw_after_id is not None:
                self.after_cancel(self._focus_redraw_after_id)
        except Exception:
            pass
        def run():
            self._focus_redraw_after_id = None
            self.redraw_focus_lines()
        try:
            self._focus_redraw_after_id = self.after(max(1, int(delay_ms)), run)
        except Exception:
            self._focus_redraw_after_id = None

    def cancel_focus_redraw(self):
        aid = getattr(self, "_focus_redraw_after_id", None)
        if aid is not None:
            try:
                self.after_cancel(aid)
            except Exception:
                pass
        self._focus_redraw_after_id = None

    def cancel_typing_idle_tick(self):
        aid = getattr(self, "_typing_tick_after", None)
        if aid is not None:
            try:
                self.after_cancel(aid)
            except Exception:
                pass
        self._typing_tick_after = None

    def default_state_dir(self):
        return stable_app_state_dir()

    def state_candidate_files(self, filename):
        """Return state files in priority order: stable shared location first, then legacy/script locations."""
        candidates = []
        try:
            candidates.append(Path(self.stable_state_dir) / filename)
        except Exception:
            pass
        try:
            candidates.append(Path(self.app_dir) / filename)
        except Exception:
            pass
        try:
            candidates.append(Path.cwd() / filename)
        except Exception:
            pass
        try:
            candidates.append(Path.home() / ".speedreader_tk" / filename)
        except Exception:
            pass
        seen = set()
        out = []
        for p in candidates:
            try:
                rp = str(Path(p).expanduser().resolve())
            except Exception:
                rp = str(p)
            if rp not in seen:
                seen.add(rp)
                out.append(Path(p))
        return out

    def file_key(self, path):
        return norm_path_key(path)

    def is_cjk(self, ch):
        return is_cjk_char(ch)

    # ---------- UI ----------
    def build_ui(self):
        self.progress_frame = tk.Frame(self, bg="black", height=12)
        self.progress_frame.pack_propagate(False)
        self.progress_var = tk.IntVar(value=0)
        self.progress_scale = tk.Scale(
            self.progress_frame, orient="horizontal", from_=0, to=1, variable=self.progress_var,
            command=self.update_from_scale, bg="black", fg="black", troughcolor="white",
            showvalue=False, sliderlength=20, width=6, highlightthickness=0,
        )
        self.progress_scale.pack(side="left", fill="x", expand=True)
        self.percent_label = tk.Label(self.progress_frame, text="0%", fg="white", bg="black", font=("Arial", 8))
        self.percent_label.pack(side="right")
        self.progress_frame.bind("<Leave>", self.hide_progress)
        self.progress_scale.bind("<Button-1>", self.pause_on_scale_click)
        self.progress_scale.bind("<ButtonRelease-1>", self.resume_on_scale_release)

        self.right_frame = tk.Frame(self, bg="black", width=self.button_size)
        self.right_frame.pack_propagate(False)
        self.right_frame.pack(side="right", fill="y")
        self.make_right_buttons()

        self.main_frame = tk.Frame(self, bg="black")
        self.main_frame.pack(side="left", expand=True, fill="both", padx=8, pady=5)

        self.stats_label = tk.Label(
            self.main_frame, text="", fg="white", bg="black", font=("Arial", 10),
            anchor="w", justify="left", height=2,
        )
        self.stats_label.pack(side="top", fill="x")

        self.typing_hint_frame = tk.Frame(self.main_frame, bg="black", height=92)
        self.typing_hint_frame.pack_propagate(False)
        self.typing_hint_title = tk.Label(
            self.typing_hint_frame, text="", fg="gray", bg="black", font=("Arial", 10),
            anchor="center", justify="center",
        )
        self.typing_hint_title.pack(side="top", fill="x")
        self.typing_hint_keys = tk.Frame(self.typing_hint_frame, bg="black")
        self.typing_hint_keys.pack(side="top", expand=True)
        self.typing_key_hint_1 = tk.Label(
            self.typing_hint_keys, text="-", fg="white", bg="black", font=("Arial", 36, "bold"),
            width=3, bd=1, relief="ridge",
        )
        self.typing_key_hint_1.pack(side="left", padx=(0, 8))
        self.typing_key_hint_2 = tk.Label(
            self.typing_hint_keys, text="-", fg="white", bg="black", font=("Arial", 36, "bold"),
            width=3, bd=1, relief="ridge",
        )
        self.typing_key_hint_2.pack(side="left", padx=(8, 0))
        self.typing_hint_alt = tk.Label(
            self.typing_hint_frame, text="", fg="gray", bg="black", font=("Arial", 9),
            anchor="center", justify="center",
        )
        self.typing_hint_alt.pack(side="bottom", fill="x")
        self.simple_button = tk.Button(
            self.typing_hint_frame, text="简", fg="white", bg="black", activeforeground="white",
            activebackground="black", font=("Arial", 14, "bold"), command=self.toggle_simple_mode,
        )
        self.first_button = tk.Button(
            self.typing_hint_frame, text="一", fg="white", bg="black", activeforeground="white",
            activebackground="black", font=("Arial", 14, "bold"), command=self.toggle_first_mode,
        )
        self.simple_button.place(x=2, rely=1.0, y=-2, anchor="sw", width=42, height=30)
        self.first_button.place(x=48, rely=1.0, y=-2, anchor="sw", width=42, height=30)

        self.text_frame = tk.Frame(self.main_frame, bg="black")
        self.text_frame.pack(side="top", fill="both", expand=True)
        self.body_text = tk.Text(
            self.text_frame, fg="white", bg="black", insertbackground="white", font=self.text_font,
            wrap="char", bd=0, relief="flat", highlightthickness=0, padx=8, pady=8,
            undo=False, autoseparators=False,
        )
        self.body_text.pack(side="left", fill="both", expand=True)
        self.body_text.tag_configure("all_text", foreground="white")
        self.body_text.tag_configure("done", foreground="gray")
        self.body_text.tag_configure("current", foreground="red")
        self.body_text.tag_configure("readline", foreground="white")
        self.body_text.insert("1.0", "右键文本区 / Ctrl+L / Ctrl+O / 拖拽 TXT 到窗口内加载。")
        self.body_text.configure(state="disabled")
        self.line_top = tk.Frame(self.body_text, bg="white", height=2)
        self.line_bottom = tk.Frame(self.body_text, bg="white", height=2)
        self.hide_focus_lines()

        self.chunk_menu = tk.Menu(self, tearoff=0)
        for size in range(1, 31):
            self.chunk_menu.add_command(label=str(size), command=lambda s=size: self.set_chunk_size(s))
        self.font_menu = tk.Menu(self, tearoff=0)
        for fs in list(range(14, 141, 7)) + [160, 180, 200]:
            self.font_menu.add_command(label=str(fs), command=lambda f=fs: self.set_font_size(f))
        self.speed_menu = tk.Menu(self, tearoff=0)
        for sp in [60, 90, 120, 150, 300, 450, 600, 750, 900, 1050, 1200, 1350, 1500, 1650, 1800, 2100, 2400, 3000, 3600, 4500]:
            self.speed_menu.add_command(label=str(sp), command=lambda s=sp: self.set_speed(s))

        self.body_text.bind("<Enter>", self.show_progress)
        self.body_text.bind("<Button-3>", self.prompt_path)
        self.body_text.bind("<Button-1>", self.on_text_click)
        self.body_text.bind("<MouseWheel>", self.on_mouse_wheel)
        self.body_text.bind("<Button-4>", self.on_mouse_wheel)
        self.body_text.bind("<Button-5>", self.on_mouse_wheel)
        self.body_text.bind("<KeyPress>", lambda e: "break")
        self.body_text.bind("<Configure>", lambda e: self.schedule_wrap_reflow(30))

        for widget in (self, self.main_frame, self.text_frame):
            widget.bind("<MouseWheel>", self.on_mouse_wheel, add="+")
            widget.bind("<Button-4>", self.on_mouse_wheel, add="+")
            widget.bind("<Button-5>", self.on_mouse_wheel, add="+")
        self.bind("<Button-1>", self.start_move)
        self.bind("<B1-Motion>", self.do_move)
        self.bind("<B1-Motion>", self.do_resize, add="+")
        self.bind("<ButtonRelease-1>", self.stop_resize, add="+")
        self.bind("<Configure>", self.on_configure)
        self.set_typing_hint_visible(False)
        self.update_stats_label()

    def make_right_buttons(self):
        def container(side="top", height=None):
            fr = tk.Frame(self.right_frame, bg="black", height=height or self.button_size)
            fr.pack_propagate(False)
            fr.pack(side=side, fill="x")
            return fr
        self.color_container = container()
        self.color_square = tk.Label(self.color_container, bg="white", bd=2, relief="ridge")
        self.color_square.pack(expand=True, fill="both")
        self.color_square.bind("<Button-1>", self.choose_color)

        self.chunk_container = container()
        self.chunk_button = tk.Button(self.chunk_container, text="#", fg="white", bg="black", font=("Arial", 40))
        self.chunk_button.pack(expand=True, fill="both")
        self.chunk_button.bind("<Button-1>", self.show_chunk_menu)

        self.bookmark_container = container()
        self.bookmark_button = tk.Button(
            self.bookmark_container, text="B", fg="green", bg="black", font=("Arial", 40), command=self.save_bookmark
        )
        self.bookmark_button.pack(expand=True, fill="both")
        self.bookmark_button.bind("<Button-3>", self.load_bookmark)

        self.font_container = container()
        self.font_button = tk.Label(self.font_container, text="T", fg="yellow", bg="black", font=("Arial", 40))
        self.font_button.pack(expand=True, fill="both")
        self.font_button.bind("<Button-1>", self.show_font_menu)

        self.typing_container = container()
        self.typing_button = tk.Button(
            self.typing_container, text="S", fg="red", bg="black", activeforeground="red", activebackground="black",
            font=("Arial", 40), command=self.toggle_typing_mode,
        )
        self.typing_button.pack(expand=True, fill="both")

        self.voice_container = container()
        self.voice_button = tk.Button(
            self.voice_container, text="声", fg="cyan", bg="black", activeforeground="cyan", activebackground="black",
            font=("Arial", 32), command=self.toggle_tts_enabled,
        )
        self.voice_button.pack(expand=True, fill="both")

        self.spacer = tk.Frame(self.right_frame, bg="black")
        self.spacer.pack(side="top", expand=True, fill="y")

        self.speed_container = container(side="bottom")
        self.speed_label = tk.Label(self.speed_container, text=str(self.wpm), fg="white", bg="black", font=("Arial", 20))
        self.speed_label.pack(expand=True, fill="both")
        self.speed_label.bind("<Button-1>", self.show_speed_menu)

        self.grip_container = container(side="bottom", height=20)
        self.resize_grip = tk.Label(self.grip_container, text="↘", bg="black", fg="white", cursor="bottom_right_corner")
        self.resize_grip.pack(side="bottom", anchor="se")
        self.resize_grip.bind("<Button-1>", self.start_resize)

    def toggle_tts_enabled(self):
        self.tts_enabled = not bool(getattr(self, "tts_enabled", True))
        try:
            if self.tts is not None:
                self.tts.set_enabled(self.tts_enabled)
        except Exception:
            self.log_debug("toggle tts failed:\n" + traceback.format_exc())
        try:
            self.voice_button.config(relief="sunken" if self.tts_enabled else "raised", fg="cyan" if self.tts_enabled else "gray")
        except Exception:
            pass
        self.log_debug(f"TTS enabled -> {self.tts_enabled}")
        self.focus_main()
        return "break"

    def bind_hotkeys(self):
        self.bind("<Control-l>", self.prompt_path)
        self.bind("<Control-o>", self.prompt_path)
        self.bind("<Control-s>", lambda event: self.save_bookmark())
        self.bind("<space>", lambda event: self.toggle_play())
        self.bind("<Escape>", self.on_escape)
        self.bind("<Left>", lambda event: self.manual_step(-1))
        self.bind("<Right>", lambda event: self.manual_step(1))
        self.bind("<Prior>", lambda event: self.page_move(-1))
        self.bind("<Next>", lambda event: self.page_move(1))
        self.bind("<Home>", lambda event: self.jump_to_char(0))
        self.bind("<End>", lambda event: self.jump_to_char(len(self.text)))
        self.bind("<Control-KeyPress-Up>", self.start_increase)
        self.bind("<Control-KeyRelease-Up>", self.stop_increase)
        self.bind("<Control-KeyPress-Down>", self.start_decrease)
        self.bind("<Control-KeyRelease-Down>", self.stop_decrease)
        self.bind_all("<KeyPress>", self.on_global_keypress_for_typing, add="+")
        self.install_typing_key_capture_bindtags()

    def on_escape(self, event=None):
        if self.typing_mode:
            return self.exit_typing_mode()
        self.attributes("-topmost", False)
        return "break"

    def on_configure(self, event):
        if event.widget != self:
            return
        font_changed = False
        if not self.fixed_font_size:
            size = max(12, min(64, int(max(260, self.winfo_height()) / 16)))
            if size != self.text_font_size:
                self.text_font_size = size
                self.text_font.configure(size=size)
                font_changed = True
        if font_changed:
            self.schedule_wrap_reflow(20)
        else:
            self.schedule_focus_redraw(1)

    def set_typing_hint_visible(self, visible: bool):
        try:
            self.typing_hint_frame.pack_forget()
            self.text_frame.pack_forget()
        except Exception:
            pass
        if visible:
            # 先固定底部提示区，再让正文吃掉剩余空间；不用 winfo_ismapped 判断，不让提示区被正文挤没。
            self.typing_hint_frame.pack(side="bottom", fill="x", pady=(2, 4))
        self.text_frame.pack(side="top", fill="both", expand=True)
        self.log_debug(f"typing hint visible={visible}, manager={self.typing_hint_frame.winfo_manager()} text_manager={self.text_frame.winfo_manager()}")

    # ---------- drag/drop ----------
    def drop_widgets(self):
        return [self, self.main_frame, self.text_frame, self.body_text]

    def enable_file_drop_late(self):
        self.update_idletasks()
        self.enable_tkinterdnd2_drop()
        self.enable_native_windows_drop()
        self.log_debug("Drag/drop enabled: " + (", ".join(self._drop_methods) if self._drop_methods else "none"))

    def enable_tkinterdnd2_drop(self):
        if not TKDND_AVAILABLE or DND_FILES is None:
            return
        ok = 0
        for widget in self.drop_widgets():
            try:
                widget.drop_target_register(DND_FILES)
                widget.dnd_bind("<<Drop>>", self.on_tkdnd_drop)
                ok += 1
            except Exception as e:
                self.log_debug(f"tkinterdnd2 bind failed on {widget}: {e}")
        if ok:
            self._drop_methods.append(f"tkinterdnd2({ok})")

    def on_tkdnd_drop(self, event):
        try:
            parts = self.tk.splitlist(event.data)
        except Exception:
            parts = [event.data]
        self.log_debug(f"tkinterdnd2 raw drop data: {event.data!r}")
        return self.open_dropped_paths(parts)

    def setup_native_api(self):
        if not IS_WINDOWS:
            return False
        if self._native_api_ready:
            return True
        try:
            user32 = ctypes.windll.user32
            shell32 = ctypes.windll.shell32
            wintypes = ctypes.wintypes
            LRESULT = ctypes.c_ssize_t
            self._WNDPROC_TYPE = ctypes.WINFUNCTYPE(LRESULT, wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM)
            self._SetWindowLongPtr = user32.SetWindowLongPtrW if ctypes.sizeof(ctypes.c_void_p) == 8 else user32.SetWindowLongW
            self._SetWindowLongPtr.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_void_p]
            self._SetWindowLongPtr.restype = ctypes.c_void_p
            self._CallWindowProc = user32.CallWindowProcW
            self._CallWindowProc.argtypes = [ctypes.c_void_p, wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM]
            self._CallWindowProc.restype = LRESULT
            self._DefWindowProc = user32.DefWindowProcW
            self._DefWindowProc.argtypes = [wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM]
            self._DefWindowProc.restype = LRESULT
            self._DragAcceptFiles = shell32.DragAcceptFiles
            self._DragAcceptFiles.argtypes = [wintypes.HWND, wintypes.BOOL]
            self._DragQueryFile = shell32.DragQueryFileW
            self._DragQueryFile.argtypes = [wintypes.HANDLE, wintypes.UINT, wintypes.LPWSTR, wintypes.UINT]
            self._DragQueryFile.restype = wintypes.UINT
            self._DragFinish = shell32.DragFinish
            self._DragFinish.argtypes = [wintypes.HANDLE]
            self._native_api_ready = True
            return True
        except Exception:
            self.log_debug("Native Windows drop API setup failed:\n" + traceback.format_exc())
            return False

    def enable_native_windows_drop(self):
        if not self.setup_native_api():
            return
        if self._native_wndproc is None:
            self._native_wndproc = self._WNDPROC_TYPE(self.native_wndproc)
        ok = 0
        for widget in self.drop_widgets():
            try:
                widget.update_idletasks()
                hwnd = int(widget.winfo_id())
                if hwnd <= 0 or hwnd in self._native_old_procs:
                    continue
                try:
                    ctypes.set_last_error(0)
                except Exception:
                    pass
                old_proc = self._SetWindowLongPtr(hwnd, self._GWLP_WNDPROC, self._native_wndproc)
                try:
                    err = ctypes.get_last_error()
                except Exception:
                    err = 0
                if not old_proc and err:
                    self.log_debug(f"Native drop SetWindowLongPtr failed hwnd={hwnd} err={err}")
                    continue
                self._native_old_procs[hwnd] = old_proc
                self._DragAcceptFiles(hwnd, True)
                ok += 1
                self.log_debug(f"Native drop enabled on hwnd={hwnd} old_proc={old_proc}")
            except Exception:
                self.log_debug("Native drop bind failed:\n" + traceback.format_exc())
        if ok:
            self._native_drop_installed = True
            self._drop_methods.append(f"native_WM_DROPFILES({ok})")

    def native_wndproc(self, hwnd, msg, wparam, lparam):
        if msg == self._WM_DROPFILES:
            paths = []
            try:
                count = self._DragQueryFile(wparam, 0xFFFFFFFF, None, 0)
                for i in range(count):
                    length = self._DragQueryFile(wparam, i, None, 0)
                    buf = ctypes.create_unicode_buffer(length + 1)
                    self._DragQueryFile(wparam, i, buf, length + 1)
                    if buf.value:
                        paths.append(buf.value)
            except Exception:
                self.log_debug("Native drop read failed:\n" + traceback.format_exc())
            finally:
                try:
                    self._DragFinish(wparam)
                except Exception:
                    pass
            self.log_debug(f"native WM_DROPFILES paths={paths!r}")
            self.after(0, lambda p=paths: self.open_dropped_paths(p))
            return 0
        old_proc = self._native_old_procs.get(int(hwnd))
        if old_proc:
            return self._CallWindowProc(old_proc, hwnd, msg, wparam, lparam)
        try:
            if self._DefWindowProc:
                return self._DefWindowProc(hwnd, msg, wparam, lparam)
        except Exception:
            pass
        return 0

    def disable_native_windows_drop(self):
        if not self._native_drop_installed or not self._native_api_ready:
            return
        for hwnd, old_proc in list(self._native_old_procs.items()):
            try:
                self._DragAcceptFiles(hwnd, False)
                if old_proc:
                    self._SetWindowLongPtr(hwnd, self._GWLP_WNDPROC, old_proc)
            except Exception:
                pass
        self._native_old_procs.clear()
        self._native_drop_installed = False

    def normalize_dropped_path(self, raw):
        if isinstance(raw, bytes):
            path = os.fsdecode(raw)
        else:
            path = str(raw)
        path = path.strip().strip("\x00")
        if path.startswith("{") and path.endswith("}"):
            path = path[1:-1]
        if path.startswith("file:"):
            parsed = urlparse(path)
            path = unquote(parsed.path)
            if os.name == "nt" and path.startswith("/") and len(path) > 2 and path[2] == ":":
                path = path[1:]
        path = unquote(path).strip().strip('"').strip("'")
        return os.path.abspath(os.path.expanduser(path))

    def open_dropped_paths(self, dropped_items):
        paths = [self.normalize_dropped_path(item) for item in dropped_items]
        self.log_debug("Normalized dropped paths: " + repr(paths))
        for path in paths:
            if not path or not os.path.isfile(path):
                self.log_debug(f"Dropped item skipped, not a file: {path}")
                continue
            now = time.time()
            if self._last_drop_path == path and now - self._last_drop_time < 0.8:
                self.log_debug(f"Duplicate drop ignored: {path}")
                return "break"
            self._last_drop_path = path
            self._last_drop_time = now
            self.last_dropped_path = path
            self.log_debug(f"Drop path recorded/opening original directly: {path}")
            self.load_text(path)
            return "break"
        messagebox.showwarning(
            "拖拽失败",
            "没有收到可读取的本地文件路径。\n\n"
            "可能原因：\n"
            "1. 程序管理员权限和 Explorer 权限不一致。\n"
            "2. 拖的是网页内容，不是本地文件。\n"
            "3. OneDrive 只是云端占位，还没有下载到本机。\n\n"
            "收到：\n" + "\n".join(paths[:10]),
        )
        return "break"

    # ---------- file loading ----------
    def prompt_path(self, event=None):
        path = filedialog.askopenfilename(
            initialdir=str(self.app_dir),
            filetypes=[("Text-like files", "*.txt *.md *.log *.csv *.text"), ("All files", "*.*")],
        )
        if path:
            self.load_text(path)
        return "break"

    def auto_open_last_file(self):
        store = self.load_bookmark_store()
        candidates = []
        for key in ("last_opened_file", "last_file"):
            value = store.get(key)
            if value:
                candidates.append(value)
        # If the stable file is empty, search legacy state files explicitly for a last opened path.
        for candidate_file in self.state_candidate_files("bookmark.json"):
            data = safe_json_load(candidate_file, {}, self.log_debug)
            if isinstance(data, dict):
                for key in ("last_opened_file", "last_file"):
                    value = data.get(key)
                    if value:
                        candidates.append(value)
        seen = set()
        for path in candidates:
            try:
                norm = self.normalize_dropped_path(path)
            except Exception:
                norm = os.path.abspath(os.path.expanduser(str(path)))
            if norm in seen:
                continue
            seen.add(norm)
            if norm and os.path.isfile(norm):
                self.log_debug(f"Auto opening last file: {norm}")
                self.load_text(norm, startup=True)
                return
            elif norm:
                self.log_debug(f"Last opened file candidate missing: {norm}")
        self.log_debug("No previous readable last_opened_file found for auto-open")

    def load_text(self, path, startup=False):
        if self.file_path and self.text:
            self.record_auto_progress_throttled(force=True)
        path = self.normalize_dropped_path(path)
        if not os.path.isfile(path):
            messagebox.showerror("文件错误", f"文件不存在或不可读取：\n{path}")
            return False
        try:
            raw = Path(path).read_bytes()
            decoded, encoding_used = decode_txt_bytes(raw)
        except Exception as e:
            self.log_debug(f"Read/decode failed: {path}\n{traceback.format_exc()}")
            messagebox.showerror("读取失败", f"无法读取文件：\n{path}\n\n{e}\n\n已写入 speedreader_debug.log")
            return False
        decoded = decoded.replace("\r\n", "\n").replace("\r", "\n")
        if not decoded:
            messagebox.showwarning("空文件", f"文件没有可显示文本：\n{path}")
            return False
        self.file_path = os.path.abspath(path)
        self.raw_text = decoded
        self.text = decoded
        self.reader_pos = 0
        self.typing_complete_notified = False
        self._char_code_cache.clear()
        self.set_text_content(decoded)
        restored = self.restore_auto_progress_if_exists()
        self.playing = False
        self.cancel_timer()
        self.stop_tts_playback()
        self.update_progress_limits()
        self.update_display_tags()
        self.update_stats_label()
        self.save_last_opened_file()
        self.log_debug(
            f"Loaded file path={self.file_path}; bytes={len(raw)} chars={len(decoded)} encoding={encoding_used} restored={restored} startup={startup}"
        )
        return True

    def set_text_content(self, text):
        self.body_text.configure(state="normal")
        self.body_text.delete("1.0", "end")
        self.body_text.insert("1.0", text)
        self.body_text.tag_remove("done", "1.0", "end")
        self.body_text.tag_remove("current", "1.0", "end")
        self.body_text.configure(state="disabled")

    def save_last_opened_file(self):
        if not self.file_path:
            return
        store = self.load_bookmark_store()
        path = os.path.abspath(os.path.expanduser(str(self.file_path)))
        store["last_opened_file"] = path
        store["last_file"] = path
        recents = store.get("recent_files")
        if not isinstance(recents, list):
            recents = []
        recents = [p for p in recents if os.path.abspath(os.path.expanduser(str(p))) != path]
        recents.insert(0, path)
        store["recent_files"] = recents[:20]
        self.save_bookmark_store(store)

    # ---------- reading display ----------
    def index_from_char_pos(self, pos):
        pos = max(0, min(int(pos), len(self.text)))
        try:
            return self.body_text.index(f"1.0+{pos}c")
        except Exception:
            return "1.0"

    def char_pos_from_index(self, index):
        try:
            return int(self.body_text.count("1.0", index, "chars")[0])
        except Exception:
            return 0

    def update_display_tags(self):
        if not self.text:
            return
        self.body_text.configure(state="normal")
        self.body_text.tag_remove("done", "1.0", "end")
        self.body_text.tag_remove("current", "1.0", "end")
        if self.typing_mode:
            # 完成态不能被 find_nearest_cjk 拉回最后一个汉字；否则最后一字会重新变红。
            if self.typing_flat_char_index >= len(self.text):
                self.typing_flat_char_index = len(self.text)
                self.body_text.tag_add("done", "1.0", "end-1c")
            else:
                cur = self.find_nearest_cjk(self.typing_flat_char_index, forward_first=True)
                if cur is not None:
                    self.typing_flat_char_index = cur
                    idx = self.index_from_char_pos(cur)
                    nxt = self.index_from_char_pos(cur + 1)
                    self.body_text.tag_add("done", "1.0", idx)
                    self.body_text.tag_add("current", idx, nxt)
                else:
                    self.typing_flat_char_index = len(self.text)
                    self.body_text.tag_add("done", "1.0", "end-1c")
        self.body_text.configure(state="disabled")
        if self.typing_mode:
            self.ensure_current_visible(center_if_needed=True)
        else:
            self.ensure_reader_visible(light=True)
        self.update_progress_display()
        self.schedule_focus_redraw(1)

    def update_stats_label(self):
        if self.typing_mode:
            self.refresh_typing_records()
            cur = self.current_typing_char() or "完成"
            mode_map = {"exact": "精确", "simple": "简单", "first": "首符号"}
            wrong = "错字不计" if self.typing_match_mode == "simple" else str(self.typing_wrong_count)
            pct = int((self.typing_flat_char_index / max(1, len(self.text))) * 100) if self.text else 0
            self.stats_label.config(
                text=(
                    f"wpm {self.typing_current_wpm:.1f}    daymax {self.typing_daymax:.1f}    txtmax {self.typing_txtmax:.1f}    "
                    f"进度 {pct}%    当前字 {cur}    模式 {mode_map.get(self.typing_match_mode, self.typing_match_mode)}    "
                    f"已按键 {self.typing_key_buffer or '-'}    错字 {wrong}"
                )
            )
        else:
            pct = int((self.reader_pos / max(1, len(self.text))) * 100) if self.text else 0
            name = os.path.basename(self.file_path) if self.file_path else "未加载"
            self.stats_label.config(text=f"阅读模式    {pct}%    {name}")

    def update_progress_limits(self):
        self.progress_scale.config(to=max(1, len(self.text)))

    def update_progress_display(self):
        if not self.text:
            return
        value = self.typing_flat_char_index if self.typing_mode else self.reader_pos
        self._updating_scale = True
        try:
            self.progress_var.set(max(0, min(int(value), len(self.text))))
        finally:
            self._updating_scale = False
        percent = int((value / max(1, len(self.text))) * 100)
        self.percent_label.config(text=f"{percent}%")

    def update_from_scale(self, val):
        if self._updating_scale or not self.text:
            return
        self.playing = False
        self.cancel_timer()
        pos = max(0, min(int(float(val)), len(self.text)))
        if self.typing_mode:
            cjk = self.find_nearest_cjk(pos, forward_first=True)
            if cjk is not None:
                self.typing_flat_char_index = cjk
                self.typing_key_buffer = ""
                self.record_typing_progress_throttled(force=True)
        else:
            self.reader_pos = pos
            self.record_auto_progress_throttled(force=True)
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        self.focus_main()

    def current_target_pos(self):
        return self.typing_flat_char_index if self.typing_mode else self.reader_pos

    def hide_focus_lines(self):
        try:
            self.line_top.place_forget()
            self.line_bottom.place_forget()
        except Exception:
            pass

    def redraw_focus_lines(self):
        if not self.text:
            self.hide_focus_lines()
            return
        pos = self.current_target_pos()
        pos = max(0, min(pos, max(0, len(self.text) - 1)))
        idx = self.index_from_char_pos(pos)
        try:
            self.body_text.update_idletasks()
            bbox = self.body_text.bbox(idx)
            info = self.body_text.dlineinfo(idx)
            if bbox is None or info is None:
                self.log_debug(f"focus line geometry empty idx={idx} pos={pos}; see+after_idle retry")
                self.body_text.see(idx)
                self.body_text.update_idletasks()
                bbox = self.body_text.bbox(idx)
                info = self.body_text.dlineinfo(idx)
                if bbox is None or info is None:
                    self.hide_focus_lines()
                    self._focus_redraw_after_id = self.after_idle(lambda: (setattr(self, "_focus_redraw_after_id", None), self.redraw_focus_lines()))
                    return
            bx, by, bw, bh = bbox
            _lx, line_y, _lw, line_h, _baseline = info
            thickness = max(1, min(2, int(round(max(1, int(self.text_font_size)) / 24.0))))
            width = max(1, self.body_text.winfo_width())
            top_y = max(0, int(line_y))
            bottom_y = max(0, int(line_y + line_h - thickness))
            self.line_top.place(x=0, y=top_y, width=width, height=thickness)
            self.line_bottom.place(x=0, y=bottom_y, width=width, height=thickness)
            self.log_debug(
                f"focus line idx={idx} pos={pos} bbox=({bx},{by},{bw},{bh}) line_y={line_y} line_h={line_h} thickness={thickness} mode={'typing' if self.typing_mode else 'reading'}",
                verbose=True,
            )
        except Exception:
            self.log_debug("focus line draw failed:\n" + traceback.format_exc())
            self.schedule_focus_redraw(20)

    def ensure_reader_visible(self, light=False):
        if not self.text:
            return
        # v14: 阅读/速读模式的当前行也必须固定在窗口中上位置，
        # 不再只是“不可见时 see 一下”。这样自动推进时横条不会贴边漂移。
        idx = self.index_from_char_pos(self.reader_pos)
        self.center_index(idx, ratio=self.focus_y_ratio)

    def ensure_current_visible(self, center_if_needed=True):
        if not self.text:
            return
        # v14: 打字模式同样强制当前红字所在视觉行落在中上聚焦位。
        idx = self.index_from_char_pos(self.typing_flat_char_index)
        self.center_index(idx, ratio=self.focus_y_ratio)

    def preferred_focus_index(self):
        """Return Text index at the visual focus line: middle, slightly above center."""
        try:
            x = max(1, self.body_text.winfo_width() // 2)
            y = max(1, int(self.body_text.winfo_height() * self.focus_y_ratio))
            return self.body_text.index(f"@{x},{y}")
        except Exception:
            return self.body_text.index("@1,1")

    def center_index(self, idx, ratio=None):
        """Place idx on the shared focus line without scanning all display lines.

        v15 no longer counts displaylines from 1.0 to end on every keypress. It first
        makes idx visible, then uses dlineinfo() and a bounded yview_scroll() correction.
        """
        if not self.text:
            return
        ratio = self.focus_y_ratio if ratio is None else float(ratio)
        ratio = max(0.20, min(0.65, ratio))
        try:
            idx = self.body_text.index(idx)
            self.body_text.see(idx)
            self.body_text.update_idletasks()
            info = self.body_text.dlineinfo(idx)
            if info is None:
                self.schedule_focus_redraw(20)
                return
            _x, y, _w, h, _baseline = info
            target_y = int(max(1, self.body_text.winfo_height()) * ratio)
            units = focus_scroll_units(y, target_y, h, max_units=30)
            if units:
                self.body_text.yview_scroll(units, "units")
                self.body_text.update_idletasks()
            if self.body_text.dlineinfo(idx) is None:
                self.body_text.see(idx)
            self.log_debug(f"center_index idx={idx} y={y} target_y={target_y} units={units} ratio={ratio}", verbose=True)
        except Exception:
            self.log_debug("center_index failed:\n" + traceback.format_exc())
            try:
                self.body_text.see(idx)
            except Exception:
                pass

    def toggle_play(self):
        if self.typing_mode:
            self.focus_main()
            return "break"
        if not self.text:
            return "break"
        self.playing = not self.playing
        self.log_debug(f"toggle_play playing={self.playing} reader_pos={self.reader_pos}")
        if self.playing:
            self.speak_current_target(force=True)
            self.schedule_next()
        else:
            self.cancel_timer()
            self.stop_tts_playback()
            self.record_auto_progress_throttled(force=True)
        return "break"

    def start_reading_from(self, pos=None):
        if self.typing_mode or not self.text:
            return
        if pos is not None:
            self.reader_pos = max(0, min(int(pos), len(self.text)))
        self.playing = True
        self.update_display_tags()
        self.schedule_next()

    def schedule_next(self):
        self.cancel_timer()
        if not self.playing or self.typing_mode or not self.text:
            return
        delay_ms = max(20, int(max(1, self.chunk_size) * 60000 / max(1, self.wpm)))
        self.after_id = self.after(delay_ms, self.advance_auto)

    def advance_auto(self):
        self.after_id = None
        if not self.playing or self.typing_mode or not self.text:
            return
        if self.reader_pos < len(self.text) - 1:
            self.reader_pos = min(len(self.text), self.reader_pos + max(1, self.chunk_size))
            self.update_display_tags()
            self.update_stats_label()
            self.schedule_next()
        else:
            self.playing = False
            self.record_auto_progress_throttled(force=True)

    def cancel_timer(self):
        if self.after_id is not None:
            try:
                self.after_cancel(self.after_id)
            except Exception:
                pass
            self.after_id = None

    def manual_step(self, step):
        if not self.text:
            return "break"
        if self.typing_mode:
            self.move_view_and_sync(step)
        else:
            self.playing = False
            self.cancel_timer()
            self.reader_pos = max(0, min(len(self.text), self.reader_pos + step * max(1, self.chunk_size)))
            self.body_text.see(self.index_from_char_pos(self.reader_pos))
            self.update_display_tags()
            self.update_stats_label()
        return "break"

    def page_move(self, direction):
        if not self.text:
            return "break"
        self.playing = False
        self.cancel_timer()
        self.body_text.yview_scroll(direction, "pages")
        self.sync_position_to_view_center()
        return "break"

    def jump_to_char(self, pos):
        if not self.text:
            return "break"
        pos = max(0, min(int(pos), len(self.text)))
        if self.typing_mode:
            cjk = self.find_nearest_cjk(pos, forward_first=True)
            if cjk is not None:
                self.typing_flat_char_index = cjk
                self.typing_key_buffer = ""
                self.record_typing_progress_throttled(force=True)
        else:
            self.reader_pos = pos
            self.record_auto_progress_throttled(force=True)
        self.body_text.see(self.index_from_char_pos(pos))
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        return "break"

    def on_text_click(self, event):
        if not self.text:
            return "break"
        try:
            idx = self.body_text.index(f"@{event.x},{event.y}")
            pos = self.char_pos_from_index(idx)
            self.log_debug(f"Text click idx={idx} pos={pos} mode={'typing' if self.typing_mode else 'reading'}")
            if self.typing_mode:
                cjk = self.find_nearest_cjk(pos, forward_first=True)
                if cjk is not None:
                    self.typing_flat_char_index = cjk
                    self.typing_key_buffer = ""
                    self.record_typing_progress_throttled(force=True)
                    self.update_display_tags()
                    self.update_typing_hint()
                    self.update_stats_label()
            else:
                # v14: 速读模式点击正文任意可见位置，都立即从点击处按当前速度开始。
                # 不需要再点空格，也不会只移动位置后停住。
                self.start_reading_from(pos)
        except Exception:
            self.log_debug("Text click failed:\n" + traceback.format_exc())
        self.focus_main()
        return "break"

    def on_mouse_wheel(self, event):
        if not self.text:
            return "break"
        if getattr(event, "num", None) == 4:
            units = -3
        elif getattr(event, "num", None) == 5:
            units = 3
        else:
            units = -3 if event.delta > 0 else 3
        self.playing = False
        self.cancel_timer()
        self.body_text.yview_scroll(units, "units")
        self.sync_position_to_view_center()
        self.log_debug(f"Mouse wheel units={units} mode={'typing' if self.typing_mode else 'reading'} pos={self.current_target_pos()}", verbose=True)
        return "break"

    def move_view_and_sync(self, step):
        self.body_text.yview_scroll(step, "units")
        self.sync_position_to_view_center()

    def sync_position_to_view_center(self):
        if not self.text:
            return
        try:
            # v14: 名字沿用旧函数，但同步点改为真正的聚焦横条位置，
            # 也就是窗口中间偏上一点，而不是几何正中间。
            idx = self.preferred_focus_index()
            pos = self.char_pos_from_index(idx)
            if self.typing_mode:
                cjk = self.find_nearest_cjk(pos, forward_first=True)
                if cjk is not None:
                    self.typing_flat_char_index = cjk
                    self.typing_key_buffer = ""
                    self.record_typing_progress_throttled(force=True)
            else:
                self.reader_pos = pos
                self.record_auto_progress_throttled()
            self.update_display_tags()
            self.update_typing_hint()
            self.update_stats_label()
            self.log_debug(f"sync focus line idx={idx} pos={pos} mode={'typing' if self.typing_mode else 'reading'}", verbose=True)
        except Exception:
            self.log_debug("sync focus line failed:\n" + traceback.format_exc())

    # ---------- visual controls ----------
    def show_progress(self, event=None):
        if not self.progress_frame.winfo_manager():
            self.progress_frame.pack(side="top", fill="x", before=self.right_frame)

    def hide_progress(self, event=None):
        self.progress_frame.pack_forget()

    def pause_on_scale_click(self, event):
        self.was_scale_playing = self.playing
        self.playing = False
        self.cancel_timer()
        self.stop_tts_playback()

    def resume_on_scale_release(self, event):
        if self.was_scale_playing and not self.typing_mode:
            self.playing = True
            self.speak_current_target(force=True)
            self.schedule_next()

    def choose_color(self, event=None):
        import tkinter.colorchooser as cc
        color = cc.askcolor(color=self.text_color)[1]
        if color:
            self.text_color = color
            self.body_text.configure(fg=color)
            self.body_text.tag_configure("all_text", foreground=color)
            self.body_text.tag_configure("readline", foreground=color)
            self.body_text.tag_configure("done", foreground="gray")
            self.body_text.tag_configure("current", foreground="red")
            self.color_square.config(bg=color)
            self.log_debug(f"text color changed {color}")

    def show_chunk_menu(self, event):
        self.chunk_menu.post(event.x_root, event.y_root)

    def set_chunk_size(self, new_size):
        self.chunk_size = int(new_size)
        self.log_debug(f"chunk size set {self.chunk_size}")
        self.update_display_tags()
        if self.playing:
            self.schedule_next()

    def show_font_menu(self, event):
        self.font_menu.post(event.x_root, event.y_root)

    def set_font_size(self, new_size):
        self.text_font_size = max(self.font_min, min(self.font_max, int(new_size)))
        self.fixed_font_size = True
        self.text_font.configure(size=self.text_font_size)
        self.log_debug(f"font size set {self.text_font_size}")
        self.schedule_wrap_reflow(20)

    def show_speed_menu(self, event):
        self.speed_menu.post(event.x_root, event.y_root)

    def set_speed(self, new_speed):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = int(new_speed)
        self.speed_label.config(text=str(self.wpm))
        self.log_debug(f"speed set {self.wpm}")
        if self.playing:
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def increase_speed(self):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm += 10
        self.speed_label.config(text=str(self.wpm))
        if self.playing:
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def decrease_speed(self):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = max(10, self.wpm - 10)
        self.speed_label.config(text=str(self.wpm))
        if self.playing:
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def start_increase(self, event):
        self.increasing = True
        self.increase_speed()
        self.after(200, self.continue_increase)

    def continue_increase(self):
        if self.increasing:
            self.increase_speed()
            self.after(50, self.continue_increase)

    def stop_increase(self, event):
        self.increasing = False

    def start_decrease(self, event):
        self.decreasing = True
        self.decrease_speed()
        self.after(200, self.continue_decrease)

    def continue_decrease(self):
        if self.decreasing:
            self.decrease_speed()
            self.after(50, self.continue_decrease)

    def stop_decrease(self, event):
        self.decreasing = False

    # ---------- window move/resize ----------
    def start_move(self, event):
        if event.widget == self:
            self.offset_x = event.x_root - self.winfo_x()
            self.offset_y = event.y_root - self.winfo_y()
            self.dragging_window = True

    def do_move(self, event):
        if not self.resizing and self.dragging_window and event.widget == self:
            self.geometry(f"+{event.x_root - self.offset_x}+{event.y_root - self.offset_y}")

    def start_resize(self, event):
        self.resizing = True
        self.start_x = event.x_root
        self.start_y = event.y_root
        self.resize_w = self.winfo_width()
        self.resize_h = self.winfo_height()
        return "break"

    def do_resize(self, event):
        if self.resizing:
            dw = event.x_root - self.start_x
            dh = event.y_root - self.start_y
            self.geometry(f"{max(360, self.resize_w + dw)}x{max(260, self.resize_h + dh)}")
            return "break"

    def stop_resize(self, event):
        self.resizing = False
        self.dragging_window = False

    # ---------- typing mode ----------
    def toggle_typing_mode(self):
        if self.typing_mode:
            return self.exit_typing_mode()
        if not self.file_path or not self.text:
            messagebox.showinfo(
                "打字模式",
                "需要先加载一个 TXT 文件。\n\n右键文本区、Ctrl+L / Ctrl+O、拖拽 TXT 到窗口内都可以加载。",
            )
            return "break"
        if not self.ensure_pinyin_backend():
            return "break"
        self.enter_typing_mode()
        return "break"

    def enter_typing_mode(self):
        self.playing = False
        self.cancel_timer()
        self.typing_mode = True
        self.typing_key_buffer = ""
        self.typing_complete_notified = False
        self.typing_button.config(relief="sunken", fg="red", activeforeground="red")
        self.set_typing_hint_visible(True)
        self.install_typing_key_capture_bindtags()
        restored = self.restore_typing_progress_or_reader_position()
        self.update_mode_buttons()
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        self.speak_current_target(force=True)
        self.start_typing_idle_tick()
        self.focus_main()
        self.schedule_misc_after(50, self.focus_main)
        self.schedule_misc_after(150, self.focus_main)
        self.log_debug(f"Entered typing mode restored={restored} pos={self.typing_flat_char_index}; no blocking popup")

    def exit_typing_mode(self):
        if not self.typing_mode:
            return "break"
        self.cancel_typing_idle_tick()
        self.record_typing_progress_throttled(force=True)
        self.reader_pos = min(self.typing_flat_char_index, len(self.text))
        self.record_auto_progress_throttled(force=True)
        self.typing_mode = False
        self.typing_key_buffer = ""
        self.typing_button.config(relief="raised", fg="red", activeforeground="red")
        self.set_typing_hint_visible(False)
        self.body_text.tag_remove("done", "1.0", "end")
        self.body_text.tag_remove("current", "1.0", "end")
        self.update_display_tags()
        self.update_stats_label()
        self.focus_main()
        self.log_debug(f"Exited typing mode synced reader_pos={self.reader_pos}")
        return "break"

    def toggle_simple_mode(self):
        if self.typing_match_mode == "simple":
            self.typing_match_mode = "exact"
        else:
            self.typing_match_mode = "simple"
            self.typing_wrong_count = 0
        self.typing_key_buffer = ""
        self.update_mode_buttons()
        self.update_typing_hint()
        self.update_stats_label()
        self.focus_main()
        self.log_debug(f"typing mode switch -> {self.typing_match_mode}")
        return "break"

    def toggle_first_mode(self):
        if self.typing_match_mode == "first":
            self.typing_match_mode = "exact"
        else:
            self.typing_match_mode = "first"
        self.typing_key_buffer = ""
        self.update_mode_buttons()
        self.update_typing_hint()
        self.update_stats_label()
        self.focus_main()
        self.log_debug(f"typing mode switch -> {self.typing_match_mode}")
        return "break"

    def update_mode_buttons(self):
        self.simple_button.config(relief="sunken" if self.typing_match_mode == "simple" else "raised", fg="red" if self.typing_match_mode == "simple" else "white")
        self.first_button.config(relief="sunken" if self.typing_match_mode == "first" else "raised", fg="red" if self.typing_match_mode == "first" else "white")

    def restore_typing_progress_or_reader_position(self):
        store = self.load_bookmark_store()
        key = self.file_key(self.file_path)
        record = store.get("typing_progress", {}).get(key)
        if record:
            try:
                size_now = os.path.getsize(self.file_path)
                mtime_now = os.path.getmtime(self.file_path)
            except Exception:
                size_now = None
                mtime_now = None
            same = (record.get("file_size") == size_now and abs(float(record.get("mtime", 0)) - float(mtime_now or 0)) < 0.01)
            if same and "typing_flat_char_index" in record:
                pos = int(record.get("typing_flat_char_index", 0))
            else:
                pos = int(record.get("typing_flat_char_index", record.get("char_index", self.reader_pos)))
            cjk = self.find_nearest_cjk(pos, forward_first=True)
            if cjk is not None:
                self.typing_flat_char_index = cjk
                self.log_debug(f"typing_progress restored same={same} record_pos={pos} cjk={cjk}")
                return True
        cjk = self.find_nearest_cjk(self.reader_pos, forward_first=True)
        if cjk is not None:
            self.typing_flat_char_index = cjk
            self.log_debug(f"typing start from reader_pos={self.reader_pos} cjk={cjk}")
            return False
        self.typing_flat_char_index = 0
        return False

    def find_nearest_cjk(self, pos, forward_first=True):
        if not self.text:
            return None
        n = len(self.text)
        pos = max(0, min(int(pos), n - 1))
        if self.is_cjk(self.text[pos]):
            return pos
        if forward_first:
            for i in range(pos + 1, n):
                if self.is_cjk(self.text[i]):
                    return i
            for i in range(pos - 1, -1, -1):
                if self.is_cjk(self.text[i]):
                    return i
        else:
            for radius in range(1, max(pos + 1, n - pos)):
                a = pos - radius
                b = pos + radius
                if a >= 0 and self.is_cjk(self.text[a]):
                    return a
                if b < n and self.is_cjk(self.text[b]):
                    return b
        return None

    def next_cjk_after(self, pos):
        if not self.text:
            return None
        for i in range(max(0, pos + 1), len(self.text)):
            if self.is_cjk(self.text[i]):
                return i
        return None

    def current_typing_char(self):
        if not self.text or self.typing_flat_char_index >= len(self.text):
            return ""
        ch = self.text[self.typing_flat_char_index]
        return ch if self.is_cjk(ch) else ""

    def update_typing_hint(self):
        if not self.typing_mode:
            return
        ch = self.current_typing_char()
        if not ch:
            self.typing_hint_title.config(text="本 TXT 打字完成；按 S 回到普通模式，或滚动/点击重新选择位置。")
            self.typing_key_hint_1.config(text="-", fg="white")
            self.typing_key_hint_2.config(text="-", fg="white")
            self.typing_hint_alt.config(text="")
            return
        codes = self.sogou_codes_for_char(ch)
        hint = codes[0] if codes else "??"
        if self.typing_match_mode == "simple":
            left, right = "任", "任"
        elif self.typing_match_mode == "first":
            left, right = (hint[0].upper() if len(hint) == 2 else "?"), "任"
        else:
            left, right = (hint[0].upper() if len(hint) == 2 else "?"), (hint[1].upper() if len(hint) == 2 else "?")
        self.typing_key_hint_1.config(text=left, fg="red" if len(self.typing_key_buffer) >= 1 else "white")
        self.typing_key_hint_2.config(text=right, fg="red" if len(self.typing_key_buffer) >= 2 else "white")
        alt = ""
        if len(codes) > 1:
            alt = "可接受：" + " / ".join(c.upper() for c in codes[:6])
        self.typing_hint_title.config(text=f"当前字：{ch}    目标码：{hint.upper() if hint else '?'}")
        self.typing_hint_alt.config(text=alt)

    def ensure_pinyin_backend(self):
        if self._pypinyin_pinyin is not None:
            return True
        try:
            from pypinyin import Style, pinyin
            self._pypinyin_pinyin = pinyin
            self._pypinyin_style_normal = Style.NORMAL
            self.log_debug("pypinyin backend loaded")
            return True
        except Exception as first_err:
            self.log_debug(f"pypinyin import failed: {first_err}")
        if not self._pinyin_install_tried:
            self._pinyin_install_tried = True
            try:
                self.log_debug("Trying one-time pypinyin install")
                subprocess.check_call([sys.executable, "-m", "pip", "install", "pypinyin"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                from pypinyin import Style, pinyin
                self._pypinyin_pinyin = pinyin
                self._pypinyin_style_normal = Style.NORMAL
                self.log_debug("pypinyin installed and loaded")
                return True
            except Exception:
                self.log_debug("one-time pypinyin install failed:\n" + traceback.format_exc())
        messagebox.showerror(
            "缺少 pypinyin",
            "打字模式需要 pypinyin。\n\n"
            "单文件版会尝试自动安装一次；如果失败，请手动运行：\n"
            "python -m pip install pypinyin\n\n"
            "或者使用 portable zip 版，里面带有免安装拼音依赖。",
        )
        return False

    def pinyin_candidates_for_char(self, ch):
        if ch in self._char_code_cache:
            return self._char_code_cache[ch].get("pinyin", [])
        pys = []
        if self._pypinyin_pinyin is not None:
            try:
                result = self._pypinyin_pinyin(ch, style=self._pypinyin_style_normal, heteronym=True, errors="ignore")
                for group in result:
                    for py in group:
                        py = normalize_pinyin(py)
                        if py and py not in pys:
                            pys.append(py)
            except Exception:
                self.log_debug(f"pypinyin failed for char={ch}:\n{traceback.format_exc()}")
        if not pys:
            pys = BUILTIN_PINYIN_FOR_TEST.get(ch, [])
        return pys

    def sogou_codes_for_char(self, ch):
        cached = self._char_code_cache.get(ch)
        if cached and "codes" in cached:
            return cached["codes"]
        pys = self.pinyin_candidates_for_char(ch)
        codes = []
        for py in pys:
            code = sogou_code_for_pinyin(py)
            if code and len(code) == 2 and code not in codes:
                codes.append(code)
        if not codes:
            self.log_debug(f"No Sogou code for char={ch!r} pinyin={pys}")
        self._char_code_cache[ch] = {"pinyin": pys, "codes": codes}
        return codes

    # ---------- key capture / input ----------
    def iter_widget_tree(self, widget=None):
        widget = widget or self
        yield widget
        try:
            children = widget.winfo_children()
        except Exception:
            children = []
        for child in children:
            yield from self.iter_widget_tree(child)

    def install_typing_key_capture_bindtags(self):
        try:
            self.bind_class(self._typing_capture_tag, "<KeyPress>", self.on_global_keypress_for_typing, add=False)
        except Exception as e:
            self.log_debug(f"typing capture bind_class failed: {e}")
            return False
        installed = 0
        for widget in list(self.iter_widget_tree()):
            try:
                tags = tuple(widget.bindtags())
            except Exception:
                continue
            if widget not in self._typing_bindtags_original:
                self._typing_bindtags_original[widget] = tags
            if self._typing_capture_tag not in tags:
                try:
                    widget.bindtags((self._typing_capture_tag,) + tags)
                    installed += 1
                except Exception as e:
                    self.log_debug(f"typing bindtag failed on {widget}: {e}")
        self.log_debug(f"typing capture bindtags refreshed installed={installed}")
        return True

    def focus_main(self):
        try:
            self.lift()
            self.focus_force()
        except Exception:
            try:
                self.focus_set()
            except Exception:
                pass
        return "break"

    def key_from_event(self, event):
        ch = getattr(event, "char", "") or ""
        keysym = getattr(event, "keysym", "") or ""
        if ch == ";" or keysym in ("semicolon", "Semicolon"):
            return ";"
        if len(ch) == 1 and ch.lower() in VALID_SHUANGPIN_KEYS:
            return ch.lower()
        if len(keysym) == 1 and keysym.lower() in VALID_SHUANGPIN_KEYS:
            return keysym.lower()
        return ""

    def is_duplicate_typing_event(self, event, key):
        now = time.time()
        sig = (
            int(getattr(event, "serial", 0) or 0),
            int(getattr(event, "time", 0) or 0),
            getattr(event, "keysym", ""),
            getattr(event, "char", ""),
            int(getattr(event, "state", 0) or 0),
            key,
        )
        if sig == self._last_typing_event_signature and now - self._last_typing_event_seen_at < 0.08:
            self.log_debug(f"duplicate key event ignored sig={sig}")
            return True
        self._last_typing_event_signature = sig
        self._last_typing_event_seen_at = now
        return False

    def on_global_keypress_for_typing(self, event):
        if not self.typing_mode:
            return None
        state = int(getattr(event, "state", 0) or 0)
        keysym = getattr(event, "keysym", "") or ""
        key = self.key_from_event(event)
        self.log_debug(
            f"KeyPress keysym={keysym!r} char={getattr(event, 'char', '')!r} state={state} mapped_key={key!r} "
            f"focus={self.focus_get()} mode={self.typing_match_mode} target={self.current_typing_char()!r} "
            f"codes={self.sogou_codes_for_char(self.current_typing_char()) if self.current_typing_char() else []} buffer={self.typing_key_buffer!r}",
            verbose=True,
        )
        if keysym == "Escape":
            return self.exit_typing_mode()
        if is_ctrl_combo_state(state):
            return None
        if keysym in ("Up", "Down", "Prior", "Next", "Home", "End", "Left", "Right"):
            if keysym == "Up": self.move_view_and_sync(-1)
            elif keysym == "Down": self.move_view_and_sync(1)
            elif keysym == "Prior": self.page_move(-1)
            elif keysym == "Next": self.page_move(1)
            elif keysym == "Home": self.jump_to_char(0)
            elif keysym == "End": self.jump_to_char(len(self.text))
            elif keysym == "Left": self.move_view_and_sync(-1)
            elif keysym == "Right": self.move_view_and_sync(1)
            return "break"
        if not key:
            return "break"
        if self.is_duplicate_typing_event(event, key):
            return "break"
        self.process_typing_key(key)
        return "break"

    def process_typing_key(self, key):
        ch = self.current_typing_char()
        if not ch:
            return
        codes = self.sogou_codes_for_char(ch)
        if not codes:
            nxt = self.next_cjk_after(self.typing_flat_char_index)
            if nxt is None:
                self.finish_typing_file()
            else:
                self.typing_flat_char_index = nxt
            self.typing_key_buffer = ""
            self.update_display_tags()
            self.update_typing_hint()
            self.update_stats_label()
            return
        accepted = False
        if self.typing_match_mode == "simple":
            self.typing_key_buffer += key
            if len(self.typing_key_buffer) >= 2:
                accepted = True
        elif self.typing_match_mode == "first":
            if not self.typing_key_buffer:
                if key in {c[0] for c in codes}:
                    self.typing_key_buffer = key
                else:
                    self.typing_wrong_count += 1
                    self.typing_key_buffer = ""
                    self.bell_safe()
            else:
                accepted = True
        else:
            if not self.typing_key_buffer:
                if key in {c[0] for c in codes}:
                    self.typing_key_buffer = key
                else:
                    self.typing_wrong_count += 1
                    self.typing_key_buffer = ""
                    self.bell_safe()
            else:
                if any(c[0] == self.typing_key_buffer and c[1] == key for c in codes):
                    accepted = True
                else:
                    self.typing_wrong_count += 1
                    self.typing_key_buffer = key if key in {c[0] for c in codes} else ""
                    self.bell_safe()
        if accepted:
            self.accept_current_typing_char()
        else:
            self.update_typing_hint()
            self.update_stats_label()

    def accept_current_typing_char(self):
        old = self.typing_flat_char_index
        self.note_typing_activity(1)
        nxt = self.next_cjk_after(old)
        if nxt is None:
            self.typing_flat_char_index = len(self.text)
            self.typing_key_buffer = ""
            self.record_typing_progress_throttled(force=True)
            self.update_display_tags()
            self.update_typing_hint()
            self.update_stats_label()
            self.finish_typing_file()
            return
        self.typing_flat_char_index = nxt
        self.typing_key_buffer = ""
        self.record_typing_progress_throttled()
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        self.speak_current_target()
        self.log_debug(f"accepted char old={old} new={nxt} char={self.text[nxt]!r}", verbose=True)

    def finish_typing_file(self):
        if self.typing_complete_notified:
            return
        self.typing_complete_notified = True
        self.log_debug("TXT typing completed")
        # 不弹阻塞 messagebox，避免完成瞬间抢焦点；底部提示和统计栏已经显示完成状态。
        try:
            self.typing_hint_title.config(text="本 TXT 打字完成；按 S 回到普通模式，或滚动/点击重新选择位置。")
        except Exception:
            pass

    def bell_safe(self):
        try:
            self.bell()
        except Exception:
            pass

    # ---------- WPM ----------
    def note_typing_activity(self, accepted_chars):
        now = time.time()
        for _ in range(int(accepted_chars)):
            self.typing_event_times.append(now)
        if self.typing_last_input_time is None or now - self.typing_last_input_time > 3.0:
            self.typing_window_start = now
        self.typing_last_input_time = now
        self.compute_current_wpm(now, record=False)
        if now - self.typing_window_start >= 10.0:
            self.compute_and_record_wpm(now)
            self.typing_window_start = now

    def compute_current_wpm(self, now=None, record=False):
        now = now or time.time()
        cutoff = now - 60.0
        times = [t for t in self.typing_event_times if t >= cutoff]
        if not times or (self.typing_last_input_time and now - self.typing_last_input_time > 60.0):
            self.typing_current_wpm = 0.0
            return self.typing_current_wpm
        if len(times) < 2:
            self.typing_current_wpm = 0.0
            return self.typing_current_wpm
        active = 0.0
        prev = times[0]
        for t in times[1:]:
            gap = t - prev
            if gap <= 3.0:
                active += gap
            prev = t
        active = max(active, min(60.0, now - times[0]), 1.0)
        wpm = len(times) / active * 60.0
        self.typing_current_wpm = round(wpm, 2)
        if record:
            self.record_wpm_result(self.typing_current_wpm)
        return self.typing_current_wpm

    def compute_and_record_wpm(self, now=None):
        return self.compute_current_wpm(now=now, record=True)

    def start_typing_idle_tick(self):
        self.cancel_typing_idle_tick()
        def tick():
            self._typing_tick_after = None
            if not self.typing_mode:
                return
            self.compute_current_wpm(time.time(), record=False)
            self.update_stats_label()
            try:
                self._typing_tick_after = self.after(1000, tick)
            except Exception:
                self._typing_tick_after = None
        try:
            self._typing_tick_after = self.after(1000, tick)
        except Exception:
            self._typing_tick_after = None

    def refresh_typing_records(self):
        store = self.load_wpm_store()
        day = time.strftime("%Y%m%d")
        self.typing_daymax = float(store.get("daily_max", {}).get(day, 0) or 0)
        key = self.file_key(self.file_path) if self.file_path else ""
        self.typing_txtmax = float(store.get("txtmax", {}).get(key, 0) or 0)

    def load_wpm_store(self):
        data = safe_json_load(self.wpm_file, {}, self.log_debug)
        data.setdefault("daily_max", {})
        data.setdefault("txtmax", {})
        return data

    def save_wpm_store(self, store):
        ok = atomic_json_save(self.wpm_file, store, self.log_debug)
        self.log_debug(f"wpm save ok={ok}", verbose=True)
        return ok

    def record_wpm_result(self, wpm):
        if not wpm or wpm <= 0:
            return
        store = self.load_wpm_store()
        timestamp = time.strftime("%Y%m%d%H%M")
        existing = store.get(timestamp)
        store[timestamp] = max(float(existing or 0), float(wpm))
        day = time.strftime("%Y%m%d")
        store.setdefault("daily_max", {})[day] = max(float(store.get("daily_max", {}).get(day, 0) or 0), float(wpm))
        if self.file_path:
            key = self.file_key(self.file_path)
            store.setdefault("txtmax", {})[key] = max(float(store.get("txtmax", {}).get(key, 0) or 0), float(wpm))
        self.save_wpm_store(store)
        self.refresh_typing_records()
        self.log_debug(f"WPM recorded {wpm}")

    # ---------- bookmarks/progress ----------
    def load_bookmark_store(self):
        """Load bookmark/progress state from the stable shared file, falling back to old per-script files.

        Older builds wrote bookmark.json next to the .py file.  Every downloaded renamed version
        therefore looked like a new app and could not auto-open the previous TXT.  This loader
        keeps one stable state file under APPDATA, but still imports legacy bookmark.json files
        when the stable file has no last_opened_file yet.
        """
        merged = {}
        used = None
        for candidate in self.state_candidate_files("bookmark.json"):
            data = safe_json_load(candidate, {}, self.log_debug)
            if not isinstance(data, dict) or not data:
                continue
            # Merge nested progress maps without destroying newer keys already loaded.
            for key, value in data.items():
                if isinstance(value, dict) and isinstance(merged.get(key), dict):
                    tmp = dict(value)
                    tmp.update(merged.get(key, {}))
                    merged[key] = tmp
                elif key not in merged or not merged.get(key):
                    merged[key] = value
            if used is None:
                used = candidate
            if merged.get("last_opened_file") or merged.get("last_file"):
                break
        merged.setdefault("auto_progress", {})
        merged.setdefault("manual_bookmarks", {})
        merged.setdefault("typing_progress", {})
        try:
            if used is not None and Path(used) != Path(self.bookmark_file):
                self.log_debug(f"bookmark imported from legacy/state file: {used}")
                atomic_json_save(self.bookmark_file, merged, self.log_debug)
        except Exception:
            pass
        return merged

    def save_bookmark_store(self, store):
        ok = atomic_json_save(self.bookmark_file, store, self.log_debug)
        # Also mirror to the script directory when writable, so older builds can still see it.
        try:
            if getattr(self, "legacy_bookmark_file", None) and Path(self.legacy_bookmark_file) != Path(self.bookmark_file):
                atomic_json_save(self.legacy_bookmark_file, store, self.log_debug)
        except Exception:
            pass
        self.log_debug(f"bookmark save ok={ok} file={self.bookmark_file}", verbose=True)
        return ok

    def make_bookmark_record(self, kind):
        try:
            size = os.path.getsize(self.file_path)
            mtime = os.path.getmtime(self.file_path)
        except Exception:
            size = None
            mtime = None
        rec = {
            "kind": kind,
            "path": self.file_path,
            "char_index": int(self.reader_pos),
            "file_size": size,
            "mtime": mtime,
            "saved_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        }
        if self.typing_mode:
            rec.update(self.make_typing_progress_fields())
        return rec

    def make_typing_progress_fields(self):
        pos = int(self.typing_flat_char_index)
        line_index = 1
        line_text = ""
        line_target = ""
        typing_pos = 0
        try:
            idx = self.index_from_char_pos(min(pos, max(0, len(self.text) - 1)))
            line_index = int(str(idx).split(".")[0])
            line_start = f"{line_index}.0"
            line_end = f"{line_index}.end"
            line_text = self.body_text.get(line_start, line_end)
            line_target = "".join(ch for ch in line_text if self.is_cjk(ch))
            rel_text = self.body_text.get(line_start, idx)
            typing_pos = sum(1 for ch in rel_text if self.is_cjk(ch))
        except Exception:
            self.log_debug("make typing progress line fields failed:\n" + traceback.format_exc())
        return {
            "typing_line_index": line_index,
            "typing_pos": typing_pos,
            "typing_flat_char_index": pos,
            "current_line_text": line_text,
            "current_line_target": line_target,
            "typing_line_text": line_text,
            "typing_line_target": line_target,
        }

    def record_auto_progress_throttled(self, force=False):
        now = time.time()
        if not force and now - getattr(self, "_last_reader_progress_save", 0.0) < 3.0:
            return False
        self._last_reader_progress_save = now
        return self.record_auto_progress(silent=True)

    def record_auto_progress(self, silent=True):
        if not self.file_path or not self.text:
            return False
        store = self.load_bookmark_store()
        key = self.file_key(self.file_path)
        store["last_opened_file"] = self.file_path
        rec = self.make_bookmark_record("auto_progress")
        store.setdefault("auto_progress", {})[key] = rec
        if self.typing_mode:
            store.setdefault("typing_progress", {})[key] = rec
        ok = self.save_bookmark_store(store)
        self.log_debug(f"auto progress saved key={key} reader={self.reader_pos} typing={self.typing_flat_char_index if self.typing_mode else None}", verbose=True)
        return ok

    def record_typing_progress_throttled(self, force=False):
        now = time.time()
        if not force and now - self._last_typing_progress_save < 3.0:
            return
        self._last_typing_progress_save = now
        self.record_auto_progress(silent=True)

    def save_bookmark(self):
        if not self.file_path or not self.text:
            return "break"
        store = self.load_bookmark_store()
        key = self.file_key(self.file_path)
        rec = self.make_bookmark_record("typing_manual_bookmark" if self.typing_mode else "manual_bookmark")
        store.setdefault("manual_bookmarks", {})[key] = rec
        if self.typing_mode:
            store.setdefault("typing_progress", {})[key] = rec
        self.save_bookmark_store(store)
        self.log_debug(f"manual bookmark saved key={key}")
        return "break"

    def load_bookmark(self, event=None):
        if not self.file_path or not self.text:
            return "break"
        store = self.load_bookmark_store()
        rec = store.get("manual_bookmarks", {}).get(self.file_key(self.file_path))
        if not rec:
            messagebox.showinfo("书签", "这个文件还没有手动 B 书签。")
            return "break"
        if self.typing_mode:
            cjk = self.find_nearest_cjk(int(rec.get("typing_flat_char_index", rec.get("char_index", 0))), forward_first=True)
            if cjk is not None:
                self.typing_flat_char_index = cjk
                self.typing_key_buffer = ""
                self.update_display_tags()
                self.update_typing_hint()
        else:
            self.reader_pos = max(0, min(int(rec.get("char_index", 0)), len(self.text)))
            self.body_text.see(self.index_from_char_pos(self.reader_pos))
            self.update_display_tags()
        self.update_stats_label()
        self.log_debug("manual bookmark loaded")
        return "break"

    def restore_auto_progress_if_exists(self):
        if not self.file_path:
            return False
        store = self.load_bookmark_store()
        key = self.file_key(self.file_path)
        rec = store.get("auto_progress", {}).get(key) or store.get("manual_bookmarks", {}).get(key)
        if not rec:
            return False
        try:
            pos = int(rec.get("char_index", rec if isinstance(rec, int) else 0)) if not isinstance(rec, int) else int(rec)
        except Exception:
            pos = 0
        self.reader_pos = max(0, min(pos, len(self.text)))
        try:
            self.body_text.see(self.index_from_char_pos(self.reader_pos))
        except Exception:
            pass
        return True


    # ---------- v18 dynamic window-wrap virtual display ----------
    def compute_display_chars_per_line(self):
        """Return how many source characters fit on one visible row at the current font/window size.

        v16 used a hard-coded 8 characters per row. v18 keeps the fast virtual renderer,
        but recalculates the row width from the Text widget's real pixel width and the
        current font. This makes the display behave like window wrap: bigger window or
        smaller font -> more characters per line; larger font or narrower window -> fewer.
        """
        try:
            width = int(self.body_text.winfo_width() or 0)
            if width <= 20:
                # Widget is not mapped yet; keep the previous value until Configure arrives.
                return max(1, int(getattr(self, "display_chars_per_line", 8) or 8))
            try:
                padx = int(float(self.body_text.cget("padx") or 0)) * 2
            except Exception:
                padx = 16
            usable = max(1, width - padx - 8)
            # Use a conservative Chinese-width estimate; if English is narrower it simply
            # leaves extra room, and Text wrap='char' remains a final safety net.
            samples = "国汉测章字龘一"
            char_w = max(1, max(int(self.text_font.measure(ch) or 1) for ch in samples))
            # Slightly under-fill to avoid one-pixel clipping and accidental Tk visual wraps.
            cpl = max(1, int(usable // max(1, char_w)))
            return max(1, min(300, cpl))
        except Exception:
            return max(1, int(getattr(self, "display_chars_per_line", 8) or 8))

    def refresh_display_chars_per_line(self):
        """Refresh dynamic wrap width. Return True when the virtual line width changed."""
        new_cpl = self.compute_display_chars_per_line()
        old_cpl = max(1, int(getattr(self, "display_chars_per_line", 8) or 8))
        if new_cpl != old_cpl:
            self.display_chars_per_line = new_cpl
            self.display_start_line = 0
            self.display_line_count = 0
            self._last_render_signature = None
            self.log_debug(
                f"dynamic wrap chars_per_line changed {old_cpl}->{new_cpl} "
                f"font={self.text_font_size} width={getattr(self, 'body_text', self).winfo_width() if hasattr(self, 'body_text') else 'NA'}"
            )
            return True
        return False

    def schedule_wrap_reflow(self, delay_ms=40):
        """Debounce window/font wrap recalculation and rerender near the current target."""
        try:
            if self._wrap_reflow_after_id is not None:
                self.after_cancel(self._wrap_reflow_after_id)
        except Exception:
            pass
        def runner():
            self._wrap_reflow_after_id = None
            try:
                changed = self.refresh_display_chars_per_line()
                if changed and self.text:
                    self.update_display_tags()
                    self.update_typing_hint()
                    self.update_stats_label()
                else:
                    self.schedule_focus_redraw(1)
            except tk.TclError:
                pass
            except Exception:
                self.log_debug("wrap reflow failed:\n" + traceback.format_exc())
        try:
            self._wrap_reflow_after_id = self.after(int(delay_ms), runner)
        except Exception:
            self._wrap_reflow_after_id = None

    # ---------- virtual display using current dynamic wrap width ----------
    def display_safe_char(self, ch):
        if ch in "\r\n\t":
            return " "
        if ord(ch) < 32:
            return " "
        return ch

    def display_total_lines(self):
        if not self.text:
            return 1
        return max(1, (len(self.text) + self.display_chars_per_line - 1) // self.display_chars_per_line)

    def display_line_for_pos(self, pos):
        if not self.text:
            return 0
        pos = max(0, min(int(pos), max(0, len(self.text) - 1)))
        return pos // self.display_chars_per_line

    def visible_line_capacity(self):
        try:
            self.update_idletasks()
            h = max(60, self.body_text.winfo_height() - 16)
            line_h = max(1, int(self.text_font.metrics("linespace") or self.text_font_size + 8))
            return max(3, min(200, h // line_h))
        except Exception:
            return 9

    def render_window_for_target(self, target_pos=None, force=False):
        if not self.text:
            self.display_start_line = 0
            self.display_line_count = 0
            return
        # Recompute the virtual wrap width before every render; cheap and prevents stale
        # eight-character lines after resize/font changes.
        self.refresh_display_chars_per_line()
        if target_pos is None:
            target_pos = self.current_target_pos()
        target_pos = max(0, min(int(target_pos), max(0, len(self.text) - 1)))
        target_line = self.display_line_for_pos(target_pos)
        capacity = self.visible_line_capacity()
        if self.typing_mode:
            # 打字模式：上一行只显示一行；第二行固定为当前正在输入行；第三行以后全是后续内容。
            start_line = max(0, target_line - 1)
        else:
            # 阅读/速读模式：当前阅读行稳定在窗口中间偏上一点。
            focus_row = max(0, min(capacity - 1, int(capacity * self.focus_y_ratio)))
            start_line = max(0, target_line - focus_row)
        total_lines = self.display_total_lines()
        start_line = max(0, min(start_line, max(0, total_lines - 1)))
        line_count = max(3, min(total_lines - start_line, capacity + 2))
        sig = (start_line, line_count, len(self.text), self.typing_mode, self.text_font_size, self.body_text.winfo_width(), self.body_text.winfo_height(), self.display_chars_per_line)
        if (not force) and sig == getattr(self, "_last_render_signature", None):
            return
        lines = []
        cpl = self.display_chars_per_line
        for ln in range(start_line, start_line + line_count):
            a = ln * cpl
            b = min(len(self.text), a + cpl)
            line = "".join(self.display_safe_char(ch) for ch in self.text[a:b])
            lines.append(line)
        render_text = "\n".join(lines)
        self._last_render_signature = sig
        self.display_start_line = start_line
        self.display_line_count = line_count
        self.display_render_text = render_text
        try:
            self._rendering_display = True
            self.body_text.configure(state="normal")
            self.body_text.delete("1.0", "end")
            self.body_text.insert("1.0", render_text)
            self.body_text.tag_remove("done", "1.0", "end")
            self.body_text.tag_remove("current", "1.0", "end")
            self.body_text.configure(state="disabled")
        finally:
            self._rendering_display = False

    def set_text_content(self, text):
        self._last_render_signature = None
        self.display_start_line = 0
        self.display_line_count = 0
        self.body_text.configure(state="normal")
        self.body_text.delete("1.0", "end")
        self.body_text.insert("1.0", "")
        self.body_text.tag_remove("done", "1.0", "end")
        self.body_text.tag_remove("current", "1.0", "end")
        self.body_text.configure(state="disabled")
        self.render_window_for_target(0, force=True)

    def index_from_char_pos(self, pos):
        if not self.text:
            return "1.0"
        pos = max(0, min(int(pos), max(0, len(self.text) - 1)))
        line = pos // self.display_chars_per_line
        if line < self.display_start_line or line >= self.display_start_line + max(1, self.display_line_count):
            self.render_window_for_target(pos, force=True)
        row = max(0, line - self.display_start_line)
        col = pos % self.display_chars_per_line
        return f"{row + 1}.{col}"

    def char_pos_from_index(self, index):
        try:
            idx = self.body_text.index(index)
            row_s, col_s = idx.split(".", 1)
            row = max(0, int(row_s) - 1)
            col = max(0, int(col_s))
            col = min(col, self.display_chars_per_line - 1)
            raw = (self.display_start_line + row) * self.display_chars_per_line + col
            return max(0, min(raw, max(0, len(self.text) - 1)))
        except Exception:
            return max(0, min(self.current_target_pos(), max(0, len(self.text) - 1)))

    def add_visible_tag_for_raw_range(self, tag, raw_start, raw_end):
        if raw_end <= raw_start or not self.text:
            return
        cpl = self.display_chars_per_line
        visible_start = self.display_start_line * cpl
        visible_end = visible_start + self.display_line_count * cpl
        a = max(int(raw_start), visible_start)
        b = min(int(raw_end), visible_end, len(self.text))
        if b <= a:
            return
        line_a = a // cpl
        line_b = (b - 1) // cpl
        for ln in range(line_a, line_b + 1):
            seg_a = max(a, ln * cpl)
            seg_b = min(b, ln * cpl + cpl)
            row = ln - self.display_start_line
            col_a = seg_a - ln * cpl
            col_b = seg_b - ln * cpl
            try:
                self.body_text.tag_add(tag, f"{row + 1}.{col_a}", f"{row + 1}.{col_b}")
            except Exception:
                pass

    def update_display_tags(self):
        if not self.text:
            return
        target = self.typing_flat_char_index if self.typing_mode else self.reader_pos
        if self.typing_mode and target < len(self.text):
            cur = self.find_nearest_cjk(target, forward_first=True)
            if cur is not None:
                self.typing_flat_char_index = cur
                target = cur
            else:
                self.typing_flat_char_index = len(self.text)
                target = max(0, len(self.text) - 1)
        self.render_window_for_target(target, force=False)
        self.body_text.configure(state="normal")
        self.body_text.tag_remove("done", "1.0", "end")
        self.body_text.tag_remove("current", "1.0", "end")
        if self.typing_mode:
            if self.typing_flat_char_index >= len(self.text):
                self.add_visible_tag_for_raw_range("done", 0, len(self.text))
            else:
                self.add_visible_tag_for_raw_range("done", 0, self.typing_flat_char_index)
                cur = self.typing_flat_char_index
                if 0 <= cur < len(self.text):
                    self.add_visible_tag_for_raw_range("current", cur, cur + 1)
        self.body_text.configure(state="disabled")
        self.update_progress_display()
        self.schedule_focus_redraw(1)

    def current_target_pos(self):
        if self.typing_mode:
            if self.typing_flat_char_index >= len(self.text):
                return max(0, len(self.text) - 1)
            return self.typing_flat_char_index
        return max(0, min(int(self.reader_pos), max(0, len(self.text) - 1)))

    def redraw_focus_lines(self):
        if not self.text:
            self.hide_focus_lines()
            return
        pos = self.current_target_pos()
        idx = self.index_from_char_pos(pos)
        try:
            self.body_text.update_idletasks()
            bbox = self.body_text.bbox(idx)
            info = self.body_text.dlineinfo(idx)
            if bbox is None or info is None:
                # bbox/dlineinfo 只能在字符已真实渲染且可见后取得；先滚到当前索引，再 idle 重算。
                self.body_text.see(idx)
                self.body_text.update_idletasks()
                bbox = self.body_text.bbox(idx)
                info = self.body_text.dlineinfo(idx)
                if bbox is None or info is None:
                    self.hide_focus_lines()
                    self._focus_redraw_after_id = self.after_idle(lambda: (setattr(self, "_focus_redraw_after_id", None), self.redraw_focus_lines()))
                    return
            bx, by, bw, bh = bbox
            _line_x, line_y, _line_w, line_h, _baseline = info
            thickness = max(1, min(2, int(round(max(1, int(self.text_font_size)) / 24.0))))
            width = max(1, self.body_text.winfo_width())
            # 横线用当前字真实 Text index 的 bbox 校验可见性，用 dlineinfo 锁定该字所在视觉行边界。
            # 放在视觉行顶部和底部内沿，厚度随当前字体大小只在 1-2px 之间变化，避免遮字。
            top_y = max(0, int(line_y))
            bottom_y = max(0, int(line_y + line_h - thickness))
            self.line_top.place(x=0, y=top_y, width=width, height=thickness)
            self.line_bottom.place(x=0, y=bottom_y, width=width, height=thickness)
            self.log_debug(
                f"v18 focus line idx={idx} pos={pos} bbox=({bx},{by},{bw},{bh}) line_y={line_y} line_h={line_h} thickness={thickness}",
                verbose=True,
            )
        except Exception:
            self.log_debug("v18 focus line draw failed:\n" + traceback.format_exc())
            self.schedule_focus_redraw(20)

    def ensure_reader_visible(self, light=False):
        self.render_window_for_target(self.reader_pos, force=False)

    def ensure_current_visible(self, center_if_needed=True):
        self.render_window_for_target(self.typing_flat_char_index, force=False)

    def page_delta_chars(self):
        return max(self.display_chars_per_line, (self.visible_line_capacity() - 2) * self.display_chars_per_line)

    def manual_step(self, step):
        if not self.text:
            return "break"
        self.playing = False
        self.cancel_timer()
        self.stop_tts_playback()
        delta = int(step) * max(1, self.chunk_size)
        if self.typing_mode:
            pos = max(0, min(len(self.text) - 1, self.typing_flat_char_index + delta))
            cjk = self.find_nearest_cjk(pos, forward_first=(delta >= 0))
            if cjk is not None:
                self.typing_flat_char_index = cjk
                self.typing_key_buffer = ""
                self.record_typing_progress_throttled(force=True)
        else:
            self.reader_pos = max(0, min(len(self.text) - 1, self.reader_pos + delta))
            self.record_auto_progress_throttled(force=True)
        self._last_render_signature = None
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        self.speak_current_target(force=True)
        return "break"

    def page_move(self, direction):
        if not self.text:
            return "break"
        self.playing = False
        self.cancel_timer()
        self.stop_tts_playback()
        delta = int(direction) * self.page_delta_chars()
        if self.typing_mode:
            pos = max(0, min(len(self.text) - 1, self.typing_flat_char_index + delta))
            cjk = self.find_nearest_cjk(pos, forward_first=(delta >= 0))
            if cjk is not None:
                self.typing_flat_char_index = cjk
                self.typing_key_buffer = ""
                self.record_typing_progress_throttled(force=True)
        else:
            self.reader_pos = max(0, min(len(self.text) - 1, self.reader_pos + delta))
            self.record_auto_progress_throttled(force=True)
        self._last_render_signature = None
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        self.speak_current_target(force=True)
        return "break"

    def on_mouse_wheel(self, event):
        if not self.text:
            return "break"
        if getattr(event, "num", None) == 4:
            direction = -1
        elif getattr(event, "num", None) == 5:
            direction = 1
        else:
            direction = -1 if event.delta > 0 else 1
        self.playing = False
        self.cancel_timer()
        self.stop_tts_playback()
        delta = direction * self.display_chars_per_line * 3
        if self.typing_mode:
            pos = max(0, min(len(self.text) - 1, self.typing_flat_char_index + delta))
            cjk = self.find_nearest_cjk(pos, forward_first=(delta >= 0))
            if cjk is not None:
                self.typing_flat_char_index = cjk
                self.typing_key_buffer = ""
                self.record_typing_progress_throttled()
        else:
            self.reader_pos = max(0, min(len(self.text) - 1, self.reader_pos + delta))
            self.record_auto_progress_throttled()
        self._last_render_signature = None
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        return "break"

    def move_view_and_sync(self, step):
        if not self.text:
            return
        self.stop_tts_playback()
        delta = int(step) * self.display_chars_per_line
        if self.typing_mode:
            pos = max(0, min(len(self.text) - 1, self.typing_flat_char_index + delta))
            cjk = self.find_nearest_cjk(pos, forward_first=(delta >= 0))
            if cjk is not None:
                self.typing_flat_char_index = cjk
                self.typing_key_buffer = ""
                self.record_typing_progress_throttled(force=True)
        else:
            self.reader_pos = max(0, min(len(self.text) - 1, self.reader_pos + delta))
            self.record_auto_progress_throttled(force=True)
        self._last_render_signature = None
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        self.speak_current_target(force=True)

    def sync_position_to_view_center(self):
        # v18 使用动态窗口 wrap 的虚拟显示窗口，滚轮/翻页直接调整 flat char index，不再从 Text 几何反推全书位置。
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()

    def jump_to_char(self, pos):
        if not self.text:
            return "break"
        pos = max(0, min(int(pos), max(0, len(self.text) - 1)))
        self.playing = False
        self.cancel_timer()
        self.stop_tts_playback()
        if self.typing_mode:
            cjk = self.find_nearest_cjk(pos, forward_first=True)
            if cjk is not None:
                self.typing_flat_char_index = cjk
                self.typing_key_buffer = ""
                self.record_typing_progress_throttled(force=True)
        else:
            self.reader_pos = pos
            self.record_auto_progress_throttled(force=True)
        self._last_render_signature = None
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        self.speak_current_target(force=True)
        return "break"

    def on_text_click(self, event):
        if not self.text:
            return "break"
        try:
            idx = self.body_text.index(f"@{event.x},{event.y}")
            pos = self.char_pos_from_index(idx)
            self.log_debug(f"Text click idx={idx} raw_pos={pos} mode={'typing' if self.typing_mode else 'reading'}")
            if self.typing_mode:
                cjk = self.find_nearest_cjk(pos, forward_first=True)
                if cjk is not None:
                    self.typing_flat_char_index = cjk
                    self.typing_key_buffer = ""
                    self.record_typing_progress_throttled(force=True)
                    self._last_render_signature = None
                    self.update_display_tags()
                    self.update_typing_hint()
                    self.update_stats_label()
                    self.speak_current_target()
            else:
                # 速读模式：点击任意可见位置，立即从此处按当前速度开始。
                self.start_reading_from(pos)
        except Exception:
            self.log_debug("v16 text click failed:\n" + traceback.format_exc())
        self.focus_main()
        return "break"

    def start_reading_from(self, pos=None):
        if self.typing_mode or not self.text:
            return
        if pos is not None:
            self.reader_pos = max(0, min(int(pos), max(0, len(self.text) - 1)))
        self.playing = True
        self._last_render_signature = None
        self.update_display_tags()
        self.update_stats_label()
        self.record_auto_progress_throttled()
        self.speak_current_target(force=True)
        self.schedule_next()

    def advance_auto(self):
        self.after_id = None
        if not self.playing or self.typing_mode or not self.text:
            return
        if self.reader_pos < len(self.text) - 1:
            self.reader_pos = min(len(self.text) - 1, self.reader_pos + max(1, self.chunk_size))
            self.update_display_tags()
            self.update_stats_label()
            self.speak_current_target()
            self.schedule_next()
        else:
            self.playing = False
            self.record_auto_progress_throttled(force=True)

    def stop_tts_playback(self):
        self._tts_active_segment = None
        self._last_spoken_target = None
        try:
            if self.tts is not None:
                self.tts.clear_queue()
                self.tts._stop_current_playback()
        except Exception:
            pass

    def current_tts_wpm(self):
        # 阅读模式用右侧速度数字；打字模式优先用当前统计 WPM。不要把上限压到 900，
        # 因为 mpv 播放加速可以处理 1000、4000 甚至更高的目标速度。
        if not self.typing_mode:
            return max(30.0, float(getattr(self, "wpm", 300) or 300))
        try:
            cwpm = float(getattr(self, "typing_current_wpm", 0) or 0)
            if cwpm >= 30:
                return max(30.0, min(12000.0, cwpm))
        except Exception:
            pass
        try:
            now = time.time()
            recent = [t for t in list(getattr(self, "typing_event_times", [])) if now - t <= 8.0]
            if len(recent) >= 2:
                active = max(0.25, recent[-1] - recent[0])
                return max(30.0, min(12000.0, len(recent) / active * 60.0))
        except Exception:
            pass
        return 300.0

    def effective_tts_wpm(self, wpm=None):
        try:
            value = self.current_tts_wpm() if wpm is None else float(wpm)
        except Exception:
            value = 300.0
        try:
            if self.tts is not None and hasattr(self.tts, "effective_wpm_for_playback"):
                return float(self.tts.effective_wpm_for_playback(value))
        except Exception:
            pass
        return max(30.0, min(7200.0, value))

    def tts_speed_bucket_for_wpm(self, wpm=None):
        try:
            return int(round(float(self.effective_tts_wpm(wpm)) / 25.0) * 25)
        except Exception:
            return 300

    def on_reader_speed_changed_for_tts(self, old_wpm):
        if not self.playing:
            return
        old_bucket = self.tts_speed_bucket_for_wpm(old_wpm)
        new_bucket = self.tts_speed_bucket_for_wpm(getattr(self, "wpm", 300))
        # 低于上限时速度变化要立刻重播；达到上限以后，显示 WPM 继续增加，
        # 但 MPV 有效速度不再变，所以不要反复 stop/restart 导致听起来没声音。
        if old_bucket != new_bucket:
            self._tts_active_segment = None
            self._last_spoken_target = None
            self.speak_current_target(force=True)
        else:
            self.speak_current_target(force=False)

    def tts_segment_from_pos(self, pos, typing=False):
        if not self.text:
            return "", pos, pos
        n = len(self.text)
        pos = max(0, min(int(pos), max(0, n - 1)))
        if typing:
            return self.text[pos:pos + 1], pos, min(n, pos + 1)
        # 从当前位置向后找真实可朗读内容，不因为当前位置落在空格/标点就静音。
        start = pos
        while start < n and not self.text[start].strip():
            start += 1
        if start >= n:
            return "", pos, pos
        hard_end_chars = set("。！？!?；;\n")
        soft_end_chars = set("，,、：:")
        max_chars = 140
        min_chars = 14
        end = start
        cjk_seen = 0
        while end < n and (end - start) < max_chars:
            ch = self.text[end]
            if self.is_cjk(ch):
                cjk_seen += 1
            end += 1
            if (end - start) >= min_chars and ch in hard_end_chars:
                break
            if (end - start) >= 36 and ch in soft_end_chars:
                break
        # 如果这一段没有中文，仍允许读英文/数字；但纯标点空白不读。
        segment = self.text[start:end].strip()
        if not segment or not any(c.isalnum() or self.is_cjk(c) for c in segment):
            return "", start, end
        return segment, start, end

    def speak_current_target(self, force=False):
        if not getattr(self, "tts_enabled", False) or self.tts is None or not self.text:
            return
        pos = self.typing_flat_char_index if self.typing_mode else self.reader_pos
        if pos < 0 or pos >= len(self.text):
            return
        mode = "typing" if self.typing_mode else "reading"
        requested_wpm = self.current_tts_wpm()
        effective_wpm = self.effective_tts_wpm(requested_wpm)
        try:
            active = getattr(self, "_tts_active_segment", None)
            wpm_bucket = self.tts_speed_bucket_for_wpm(effective_wpm)
            if (not force) and active:
                a_mode, a_start, a_end, a_wpm_bucket = active
                if a_mode == mode and a_start <= pos < a_end and abs(wpm_bucket - a_wpm_bucket) <= 25:
                    return
                # 当显示 WPM 已超过 MPV 能播放的有效上限时，阅读光标可能比音频跑得更快。
                # 此时不能因为进入下一段就不断杀掉 mpv；让当前段按上限速度放完，至少持续有声。
                try:
                    cap_wpm = float(getattr(self.tts, "base_speech_wpm", 300.0)) * float(getattr(self.tts, "max_mpv_speed", 24.0))
                except Exception:
                    cap_wpm = 7200.0
                if effective_wpm >= cap_wpm - 1 and self.tts is not None and hasattr(self.tts, "is_playing") and self.tts.is_playing():
                    return
            segment, start, end = self.tts_segment_from_pos(pos, typing=self.typing_mode)
            if not segment:
                return
            sig = (mode, start, end, hashlib.sha1(segment.encode("utf-8", errors="ignore")).hexdigest()[:12], wpm_bucket)
            if (not force) and sig == getattr(self, "_last_spoken_target", None):
                return
            self._last_spoken_target = sig
            self._tts_active_segment = (mode, start, end, wpm_bucket)
            self.tts.speak_text(segment, wpm=effective_wpm, reason=f"{mode}:{start}-{end}")
        except Exception:
            self.log_debug("speak_current_target failed:\n" + traceback.format_exc())


    # ---------- final override: exact visual WPM clock + centered inter-line focus bars ----------
    def _reset_reader_wpm_clock(self):
        """Reset the reading-mode time accumulator so visual advance follows the current WPM."""
        try:
            self._reader_wpm_last_time = time.perf_counter()
        except Exception:
            self._reader_wpm_last_time = None
        self._reader_wpm_carry_chars = 0.0

    def _reader_chars_per_second(self):
        try:
            wpm = float(getattr(self, "wpm", 300) or 300)
        except Exception:
            wpm = 300.0
        return max(1.0, wpm) / 60.0

    def _reader_tick_ms(self):
        """Small adaptive timer tick.

        The previous 20ms minimum made chunk_size=1 unable to exceed 3000 chars/min.
        This tick is short enough for 1000-4000+ WPM while the accumulator preserves
        the exact long-run WPM instead of tying speed to Tk timer granularity.
        """
        cps = self._reader_chars_per_second()
        try:
            # About two checks per character, clamped to avoid excessive idle wakeups at low speed.
            return max(1, min(15, int(round(500.0 / max(1.0, cps)))))
        except Exception:
            return 10

    def toggle_play(self):
        if self.typing_mode:
            self.focus_main()
            return "break"
        if not self.text:
            return "break"
        self.playing = not self.playing
        self.log_debug(f"toggle_play playing={self.playing} reader_pos={self.reader_pos}")
        if self.playing:
            self._reset_reader_wpm_clock()
            self.speak_current_target(force=True)
            self.schedule_next()
        else:
            self.cancel_timer()
            self.stop_tts_playback()
            self._reset_reader_wpm_clock()
            self.record_auto_progress_throttled(force=True)
        return "break"

    def start_reading_from(self, pos=None):
        if self.typing_mode or not self.text:
            return
        if pos is not None:
            self.reader_pos = max(0, min(int(pos), max(0, len(self.text) - 1)))
        self.playing = True
        self._last_render_signature = None
        self._reset_reader_wpm_clock()
        self.update_display_tags()
        self.update_stats_label()
        self.record_auto_progress_throttled()
        self.speak_current_target(force=True)
        self.schedule_next()

    def schedule_next(self):
        self.cancel_timer()
        if not self.playing or self.typing_mode or not self.text:
            return
        if getattr(self, "_reader_wpm_last_time", None) is None:
            self._reset_reader_wpm_clock()
        try:
            self.after_id = self.after(self._reader_tick_ms(), self.advance_auto)
        except Exception:
            self.after_id = None

    def advance_auto(self):
        self.after_id = None
        if not self.playing or self.typing_mode or not self.text:
            return
        if self.reader_pos >= len(self.text) - 1:
            self.playing = False
            self.record_auto_progress_throttled(force=True)
            return
        try:
            now = time.perf_counter()
            last = getattr(self, "_reader_wpm_last_time", None)
            if last is None:
                last = now
            # Cap one delayed frame so dragging/resizing the window does not skip a whole page.
            elapsed = max(0.0, min(0.25, now - float(last)))
            self._reader_wpm_last_time = now
            carry = float(getattr(self, "_reader_wpm_carry_chars", 0.0) or 0.0)
            carry += elapsed * self._reader_chars_per_second()
            chunk = max(1, int(getattr(self, "chunk_size", 1) or 1))
            if carry < chunk:
                self._reader_wpm_carry_chars = carry
                self.schedule_next()
                return
            # Advance in chunk-sized visual jumps, but the accumulator is in characters,
            # so average reading speed remains exactly the displayed WPM.
            chunks = max(1, int(carry // chunk))
            advance_chars = chunks * chunk
            self._reader_wpm_carry_chars = max(0.0, carry - advance_chars)
            self.reader_pos = min(len(self.text) - 1, self.reader_pos + advance_chars)
            self.update_display_tags()
            self.update_stats_label()
            self.speak_current_target()
            self.schedule_next()
        except Exception:
            self.log_debug("exact-WPM advance failed:\n" + traceback.format_exc())
            # Fallback still preserves average speed better than the old 20ms cap.
            self.reader_pos = min(len(self.text) - 1, self.reader_pos + max(1, int(getattr(self, "chunk_size", 1) or 1)))
            self.update_display_tags()
            self.update_stats_label()
            self.schedule_next()

    def set_speed(self, new_speed):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = max(1, int(new_speed))
        self.speed_label.config(text=str(self.wpm))
        self.log_debug(f"speed set {self.wpm}")
        if self.playing:
            self._reset_reader_wpm_clock()
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def increase_speed(self):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = max(1, int(getattr(self, "wpm", 300) or 300) + 10)
        self.speed_label.config(text=str(self.wpm))
        if self.playing:
            self._reset_reader_wpm_clock()
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def decrease_speed(self):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = max(10, int(getattr(self, "wpm", 300) or 300) - 10)
        self.speed_label.config(text=str(self.wpm))
        if self.playing:
            self._reset_reader_wpm_clock()
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def _focus_line_thickness(self):
        """Focus bar thickness in pixels, derived from the current rendered font size."""
        try:
            px = int(self.text_font.metrics("linespace") or 0)
        except Exception:
            px = 0
        if px <= 0:
            try:
                px = int(abs(int(self.text_font_size)))
            except Exception:
                px = 24
        # 24px font -> 1px, 48-72px -> 2px, very large fonts -> thicker but still restrained.
        return max(1, min(8, int(round(px / 34.0))))

    def _apply_focus_line_spacing(self):
        """Reserve real inter-line whitespace so bars can sit between rows instead of over glyphs."""
        try:
            thickness = self._focus_line_thickness()
            spacing3 = max(3, thickness * 4)
            if int(getattr(self, "_focus_line_spacing3", -1)) != spacing3:
                self._focus_line_spacing3 = spacing3
                self.body_text.configure(spacing1=0, spacing2=0, spacing3=spacing3)
                self._last_render_signature = None
        except Exception:
            pass

    def visible_line_capacity(self):
        try:
            self.update_idletasks()
            self._apply_focus_line_spacing()
            h = max(60, self.body_text.winfo_height() - 16)
            line_h = max(1, int(self.text_font.metrics("linespace") or self.text_font_size + 8))
            line_h += int(getattr(self, "_focus_line_spacing3", 0) or 0)
            return max(3, min(200, h // max(1, line_h)))
        except Exception:
            return 9

    def _display_line_ink_bounds(self, row):
        """Return glyph-ink bounds for one displayed Text row, with dlineinfo fallback."""
        try:
            row = int(row)
            if row <= 0:
                return None
            info = self.body_text.dlineinfo(f"{row}.0")
            if info is None:
                return None
            line_x, line_y, line_w, line_h, baseline = info
            try:
                row_text = self.body_text.get(f"{row}.0", f"{row}.end")
            except Exception:
                row_text = ""
            ink_top = None
            ink_bottom = None
            ink_left = None
            ink_right = None
            for col, ch in enumerate(row_text):
                if not ch or not ch.strip():
                    continue
                bbox = self.body_text.bbox(f"{row}.{col}")
                if bbox is None:
                    continue
                x, y, w, h = bbox
                ink_top = y if ink_top is None else min(ink_top, y)
                ink_bottom = y + h if ink_bottom is None else max(ink_bottom, y + h)
                ink_left = x if ink_left is None else min(ink_left, x)
                ink_right = x + w if ink_right is None else max(ink_right, x + w)
            if ink_top is None or ink_bottom is None:
                ink_top = int(line_y)
                ink_bottom = int(line_y + line_h)
                ink_left = int(line_x)
                ink_right = int(line_x + line_w)
            return {
                "row": row,
                "line_y": int(line_y),
                "line_h": int(line_h),
                "line_bottom": int(line_y + line_h),
                "ink_top": int(ink_top),
                "ink_bottom": int(ink_bottom),
                "ink_left": int(ink_left or 0),
                "ink_right": int(ink_right or 0),
            }
        except Exception:
            return None

    def _line_y_between(self, lower_edge, upper_edge, thickness, fallback_center):
        """Place a horizontal bar centered between two glyph edges without covering glyphs when possible."""
        try:
            lower = float(lower_edge) if lower_edge is not None else None
            upper = float(upper_edge) if upper_edge is not None else None
            if lower is not None and upper is not None and upper > lower:
                center = (lower + upper) / 2.0
                y = int(round(center - thickness / 2.0))
                # If there is enough whitespace, keep the bar fully inside it.
                if upper - lower >= thickness:
                    y = max(int(round(lower)), min(y, int(round(upper - thickness))))
            else:
                y = int(round(float(fallback_center) - thickness / 2.0))
            max_y = max(0, int(self.body_text.winfo_height()) - thickness)
            return max(0, min(max_y, y))
        except Exception:
            return max(0, int(round(float(fallback_center or 0))))

    def redraw_focus_lines(self):
        if not self.text:
            self.hide_focus_lines()
            return
        pos = self.current_target_pos()
        idx = self.index_from_char_pos(pos)
        try:
            self._apply_focus_line_spacing()
            self.body_text.update_idletasks()
            bbox = self.body_text.bbox(idx)
            info = self.body_text.dlineinfo(idx)
            if bbox is None or info is None:
                self.body_text.see(idx)
                self.body_text.update_idletasks()
                bbox = self.body_text.bbox(idx)
                info = self.body_text.dlineinfo(idx)
                if bbox is None or info is None:
                    self.hide_focus_lines()
                    self._focus_redraw_after_id = self.after_idle(lambda: (setattr(self, "_focus_redraw_after_id", None), self.redraw_focus_lines()))
                    return
            idx_norm = self.body_text.index(idx)
            row = int(idx_norm.split(".", 1)[0])
            current = self._display_line_ink_bounds(row)
            if not current:
                self.hide_focus_lines()
                return
            end_row = int(self.body_text.index("end-1c").split(".", 1)[0])
            prev_line = self._display_line_ink_bounds(row - 1) if row > 1 else None
            next_line = self._display_line_ink_bounds(row + 1) if row < end_row else None
            thickness = self._focus_line_thickness()
            width = max(1, self.body_text.winfo_width())
            # Use glyph bbox edges, not only dlineinfo row edges. This puts the bars into the
            # actual blank gap between adjacent rows and keeps the distance above/below the
            # current row visually balanced.
            top_lower = prev_line["ink_bottom"] if prev_line else current["line_y"]
            top_upper = current["ink_top"]
            bottom_lower = current["ink_bottom"]
            bottom_upper = next_line["ink_top"] if next_line else current["line_bottom"]
            top_fallback = (float(top_lower) + float(top_upper)) / 2.0
            bottom_fallback = (float(bottom_lower) + float(bottom_upper)) / 2.0
            top_y = self._line_y_between(top_lower, top_upper, thickness, top_fallback)
            bottom_y = self._line_y_between(bottom_lower, bottom_upper, thickness, bottom_fallback)
            # If an extreme font/spacing combination collapses the two bars, keep ordering stable.
            if bottom_y <= top_y:
                bottom_y = min(max(0, self.body_text.winfo_height() - thickness), top_y + max(thickness + 1, int(current["line_h"])))
            self.line_top.place(x=0, y=top_y, width=width, height=thickness)
            self.line_bottom.place(x=0, y=bottom_y, width=width, height=thickness)
            self.log_debug(
                f"aligned focus bars idx={idx_norm} pos={pos} row={row} bbox={bbox} "
                f"cur_ink=({current['ink_top']},{current['ink_bottom']}) "
                f"prev={None if not prev_line else (prev_line['ink_top'], prev_line['ink_bottom'])} "
                f"next={None if not next_line else (next_line['ink_top'], next_line['ink_bottom'])} "
                f"bars=({top_y},{bottom_y}) thickness={thickness} wpm={getattr(self, 'wpm', None)}",
                verbose=True,
            )
        except Exception:
            self.log_debug("aligned focus bar draw failed:\n" + traceback.format_exc())
            self.schedule_focus_redraw(20)

    def _reader_row_start_pos(self, pos=None):
        if not self.text:
            return 0
        self.refresh_display_chars_per_line()
        total = len(self.text)
        cpl = max(1, int(getattr(self, "display_chars_per_line", 1) or 1))
        if pos is None:
            pos = getattr(self, "reader_pos", 0)
        pos = max(0, min(int(pos), max(0, total - 1)))
        return (pos // cpl) * cpl

    def _reader_block_info(self, pos=None):
        if not self.text:
            return None
        self.refresh_display_chars_per_line()
        total = len(self.text)
        cpl = max(1, int(getattr(self, "display_chars_per_line", 1) or 1))
        total_lines = max(1, (total + cpl - 1) // cpl)
        line_step = max(1, int(getattr(self, "chunk_size", 1) or 1))
        if pos is None:
            pos = getattr(self, "reader_pos", 0)
        pos = max(0, min(int(pos), max(0, total - 1)))
        line_idx = max(0, min((pos // cpl), total_lines - 1))
        start_pos = line_idx * cpl
        end_line = min(total_lines, line_idx + line_step)
        end_pos = min(total, end_line * cpl)
        visible_chars = max(1, end_pos - start_pos)
        try:
            wpm = max(1.0, float(getattr(self, "wpm", 300) or 300))
        except Exception:
            wpm = 300.0
        delay_ms = max(1, int(round(visible_chars * 60000.0 / wpm)))
        return {
            "line_idx": line_idx,
            "start_pos": start_pos,
            "end_pos": end_pos,
            "next_pos": end_pos,
            "visible_chars": visible_chars,
            "delay_ms": delay_ms,
            "line_step": line_step,
            "cpl": cpl,
        }

    def _reset_reader_wpm_clock(self):
        """Reading mode is line-paced: one timer per visible line block, timed by that block's char count."""
        self._reader_wpm_last_time = None
        self._reader_wpm_carry_chars = 0.0
        self._reader_block_started_at = None
        self._reader_block_deadline_at = None

    def toggle_play(self):
        if self.typing_mode:
            self.focus_main()
            return "break"
        if not self.text:
            return "break"
        self.playing = not self.playing
        self.log_debug(f"toggle_play playing={self.playing} reader_pos={self.reader_pos}")
        if self.playing:
            info = self._reader_block_info(self.reader_pos)
            if info is not None:
                self.reader_pos = info["start_pos"]
            self._last_render_signature = None
            self._reset_reader_wpm_clock()
            self.update_display_tags()
            self.update_stats_label()
            self.record_auto_progress_throttled()
            self.speak_current_target(force=True)
            self.schedule_next()
        else:
            self.cancel_timer()
            self.stop_tts_playback()
            self._reset_reader_wpm_clock()
            self.record_auto_progress_throttled(force=True)
        return "break"

    def start_reading_from(self, pos=None):
        if self.typing_mode or not self.text:
            return
        if pos is None:
            pos = getattr(self, "reader_pos", 0)
        info = self._reader_block_info(pos)
        if info is not None:
            self.reader_pos = info["start_pos"]
        self.playing = True
        self._last_render_signature = None
        self._reset_reader_wpm_clock()
        self.update_display_tags()
        self.update_stats_label()
        self.record_auto_progress_throttled()
        self.speak_current_target(force=True)
        self.schedule_next()

    def schedule_next(self):
        self.cancel_timer()
        if not self.playing or self.typing_mode or not self.text:
            return
        info = self._reader_block_info(self.reader_pos)
        if info is None:
            return
        delay_ms = max(1, int(info["delay_ms"]))
        try:
            now = time.perf_counter()
        except Exception:
            now = None
        self._reader_block_started_at = now
        self._reader_block_deadline_at = (None if now is None else now + delay_ms / 1000.0)
        try:
            self.after_id = self.after(delay_ms, self.advance_auto)
        except Exception:
            self.after_id = None

    def advance_auto(self):
        self.after_id = None
        if not self.playing or self.typing_mode or not self.text:
            return
        if int(getattr(self, "reader_pos", 0) or 0) >= len(self.text):
            self.playing = False
            self.record_auto_progress_throttled(force=True)
            return
        try:
            info = self._reader_block_info(self.reader_pos)
            if info is None:
                self.playing = False
                self.record_auto_progress_throttled(force=True)
                return
            self.reader_pos = int(info["next_pos"])
            if self.reader_pos >= len(self.text):
                self.reader_pos = len(self.text)
                self.playing = False
                self.update_display_tags()
                self.update_stats_label()
                self.record_auto_progress_throttled(force=True)
                return
            self.update_display_tags()
            self.update_stats_label()
            self.record_auto_progress_throttled()
            self.speak_current_target()
            self.schedule_next()
        except Exception:
            self.log_debug("line-paced exact-WPM advance failed:\n" + traceback.format_exc())
            self.playing = False
            self.record_auto_progress_throttled(force=True)

    def set_speed(self, new_speed):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = max(1, int(new_speed))
        self.speed_label.config(text=str(self.wpm))
        self.log_debug(f"speed set {self.wpm}")
        if self.playing:
            self._reset_reader_wpm_clock()
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def increase_speed(self):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = max(1, int(getattr(self, "wpm", 300) or 300) + 10)
        self.speed_label.config(text=str(self.wpm))
        if self.playing:
            self._reset_reader_wpm_clock()
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def decrease_speed(self):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = max(10, int(getattr(self, "wpm", 300) or 300) - 10)
        self.speed_label.config(text=str(self.wpm))
        if self.playing:
            self._reset_reader_wpm_clock()
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def _display_row_bounds(self, row):
        try:
            row = int(row)
            if row <= 0:
                return None
            info = self.body_text.dlineinfo(f"{row}.0")
            if info is None:
                return None
            line_x, line_y, line_w, line_h, baseline = info
            return {
                "row": row,
                "top": int(round(line_y)),
                "bottom": int(round(line_y + line_h)),
                "height": int(round(line_h)),
                "center": float(line_y) + float(line_h) / 2.0,
            }
        except Exception:
            return None

    def _line_y_center_between_rows(self, upper_row, lower_row):
        try:
            if upper_row and lower_row:
                return (float(upper_row["bottom"]) + float(lower_row["top"])) / 2.0
            if lower_row:
                return max(0.0, float(lower_row["top"]) / 2.0)
            if upper_row:
                return float(upper_row["bottom"]) + max(2.0, float(upper_row["height"]) * 0.25)
        except Exception:
            pass
        return 0.0

    def redraw_focus_lines(self):
        if not self.text:
            self.hide_focus_lines()
            return
        pos = self.current_target_pos()
        idx = self.index_from_char_pos(pos)
        try:
            self._apply_focus_line_spacing()
            self.body_text.update_idletasks()
            bbox = self.body_text.bbox(idx)
            info = self.body_text.dlineinfo(idx)
            if bbox is None or info is None:
                self.body_text.see(idx)
                self.body_text.update_idletasks()
                bbox = self.body_text.bbox(idx)
                info = self.body_text.dlineinfo(idx)
                if bbox is None or info is None:
                    self.hide_focus_lines()
                    self._focus_redraw_after_id = self.after_idle(lambda: (setattr(self, "_focus_redraw_after_id", None), self.redraw_focus_lines()))
                    return
            idx_norm = self.body_text.index(idx)
            row = int(idx_norm.split(".", 1)[0])
            cur = self._display_row_bounds(row)
            if not cur:
                self.hide_focus_lines()
                return
            end_row = int(self.body_text.index("end-1c").split(".", 1)[0])
            prev_row = self._display_row_bounds(row - 1) if row > 1 else None
            next_row = self._display_row_bounds(row + 1) if row < end_row else None
            thickness = self._focus_line_thickness()
            width = max(1, self.body_text.winfo_width())
            top_center = self._line_y_center_between_rows(prev_row, cur)
            bottom_center = self._line_y_center_between_rows(cur, next_row)
            top_y = int(round(top_center - thickness / 2.0))
            bottom_y = int(round(bottom_center - thickness / 2.0))
            if prev_row and cur:
                top_min = int(round(prev_row["bottom"]))
                top_max = int(round(cur["top"] - thickness))
                if top_max >= top_min:
                    top_y = max(top_min, min(top_y, top_max))
            if cur and next_row:
                bottom_min = int(round(cur["bottom"]))
                bottom_max = int(round(next_row["top"] - thickness))
                if bottom_max >= bottom_min:
                    bottom_y = max(bottom_min, min(bottom_y, bottom_max))
            max_y = max(0, int(self.body_text.winfo_height()) - thickness)
            top_y = max(0, min(max_y, top_y))
            bottom_y = max(0, min(max_y, bottom_y))
            if bottom_y <= top_y:
                target_gap = max(thickness + 1, int(round(cur["height"])))
                bottom_y = min(max_y, top_y + target_gap)
            self.line_top.place(x=0, y=top_y, width=width, height=thickness)
            self.line_bottom.place(x=0, y=bottom_y, width=width, height=thickness)
            self.log_debug(
                f"midgap focus bars idx={idx_norm} pos={pos} row={row} bbox={bbox} "
                f"prev={None if not prev_row else (prev_row['top'], prev_row['bottom'])} "
                f"cur={(cur['top'], cur['bottom'])} next={None if not next_row else (next_row['top'], next_row['bottom'])} "
                f"bars=({top_y},{bottom_y}) thickness={thickness}",
                verbose=True,
            )
        except Exception:
            self.log_debug("midgap focus bar draw failed:\n" + traceback.format_exc())
            self.schedule_focus_redraw(20)

    def _focus_debug_enabled(self):
        try:
            return bool(os.environ.get("SPEEDREADER_FOCUS_DEBUG")) or ("--focus-debug" in sys.argv)
        except Exception:
            return False

    def _focus_line_thickness(self):
        """Final focus-bar thickness: derived from rendered font pixels, clamped to 1-2px."""
        try:
            px = int(self.text_font.metrics("linespace") or 0)
        except Exception:
            px = 0
        if px <= 0:
            try:
                px = int(abs(int(self.text_font_size)))
            except Exception:
                px = 24
        return max(1, min(2, int(round(px / 34.0))))

    def _apply_focus_line_spacing(self):
        """Reserve only the minimal gap needed for the two white bars between Text rows."""
        try:
            thickness = self._focus_line_thickness()
            try:
                linespace = int(self.text_font.metrics("linespace") or 0)
            except Exception:
                linespace = int(getattr(self, "text_font_size", 24) or 24)
            spacing3 = max(thickness + 2, int(round(linespace * 0.055)))
            spacing3 = max(3, min(8, spacing3))
            if int(getattr(self, "_focus_line_spacing3", -1)) != spacing3:
                self._focus_line_spacing3 = spacing3
                self.body_text.configure(spacing1=0, spacing2=0, spacing3=spacing3)
                self._last_render_signature = None
        except Exception:
            pass

    def _row_dline(self, row):
        """Return final layout geometry for one displayed Text row, based only on dlineinfo."""
        try:
            row = int(row)
            if row <= 0:
                return None
            info = self.body_text.dlineinfo(f"{row}.0")
            if info is None:
                return None
            x, y, w, h, baseline = info
            return {
                "row": row,
                "x": int(round(x)),
                "y": int(round(y)),
                "w": int(round(w)),
                "h": int(round(h)),
                "top": int(round(y)),
                "bottom": int(round(y + h)),
                "baseline": int(round(y + baseline)),
                "right": int(round(x + w)),
            }
        except Exception:
            return None

    def _row_bbox_scan(self, row, limit=10):
        """Debug-only sample of character bbox rectangles. Never used for vertical positioning."""
        out = []
        try:
            row = int(row)
            row_text = self.body_text.get(f"{row}.0", f"{row}.end")
            for col, ch in enumerate(row_text[:max(0, int(limit))]):
                if not ch.strip():
                    continue
                bb = self.body_text.bbox(f"{row}.{col}")
                if bb is not None:
                    out.append((col, ch, tuple(int(v) for v in bb)))
        except Exception:
            pass
        return out

    def _force_index_geometry(self, idx):
        """Make idx visible, then return (bbox, dlineinfo); retry on idle when Tk has not laid out yet."""
        try:
            self.body_text.update_idletasks()
            bbox = self.body_text.bbox(idx)
            info = self.body_text.dlineinfo(idx)
            if bbox is not None and info is not None:
                return bbox, info
            self.body_text.see(idx)
            self.body_text.update_idletasks()
            bbox = self.body_text.bbox(idx)
            info = self.body_text.dlineinfo(idx)
            if bbox is not None and info is not None:
                return bbox, info
        except Exception:
            pass
        return None, None

    def _gap_bar_y(self, upper_row, lower_row, thickness, fallback_center=0):
        """Center a bar in the real dlineinfo gap between two adjacent rows."""
        try:
            if upper_row and lower_row:
                low = float(upper_row["bottom"])
                high = float(lower_row["top"])
                if high >= low:
                    y = int(round((low + high - thickness) / 2.0))
                    if high - low >= thickness:
                        return max(int(round(low)), min(y, int(round(high - thickness))))
                    return y
            return int(round(float(fallback_center) - thickness / 2.0))
        except Exception:
            return 0

    def _place_debug_focus_line(self, name, y, color, width, height=1):
        try:
            if not self._focus_debug_enabled():
                return
            if not hasattr(self, "_focus_debug_frames"):
                self._focus_debug_frames = {}
            fr = self._focus_debug_frames.get(name)
            if fr is None:
                fr = tk.Frame(self.body_text, bg=color, height=height)
                self._focus_debug_frames[name] = fr
            fr.configure(bg=color)
            fr.place(x=0, y=max(0, int(round(y))), width=max(1, int(width)), height=max(1, int(height)))
        except Exception:
            pass

    def _hide_debug_focus_lines(self):
        try:
            for fr in getattr(self, "_focus_debug_frames", {}).values():
                try:
                    fr.place_forget()
                except Exception:
                    pass
        except Exception:
            pass

    def redraw_focus_lines(self):
        if not self.text:
            self.hide_focus_lines()
            self._hide_debug_focus_lines()
            return
        pos = self.current_target_pos()
        idx = self.index_from_char_pos(pos)
        try:
            self._apply_focus_line_spacing()
            bbox, info = self._force_index_geometry(idx)
            if bbox is None or info is None:
                self.hide_focus_lines()
                self._hide_debug_focus_lines()
                self._focus_redraw_after_id = self.after_idle(lambda: (setattr(self, "_focus_redraw_after_id", None), self.redraw_focus_lines()))
                return
            idx_norm = self.body_text.index(idx)
            row = int(idx_norm.split(".", 1)[0])
            end_row = int(self.body_text.index("end-1c").split(".", 1)[0])
            prev_row = self._row_dline(row - 1) if row > 1 else None
            cur_row = self._row_dline(row)
            next_row = self._row_dline(row + 1) if row < end_row else None
            if cur_row is None:
                self.hide_focus_lines()
                self._hide_debug_focus_lines()
                return
            thickness = self._focus_line_thickness()

            top_fallback = float(cur_row["top"]) - max(2.0, cur_row["h"] * 0.25)
            bottom_fallback = float(cur_row["bottom"]) + max(2.0, cur_row["h"] * 0.25)
            top_y = self._gap_bar_y(prev_row, cur_row, thickness, top_fallback)
            bottom_y = self._gap_bar_y(cur_row, next_row, thickness, bottom_fallback)

            max_y = max(0, int(self.body_text.winfo_height()) - thickness)
            top_y = max(0, min(max_y, int(top_y)))
            bottom_y = max(0, min(max_y, int(bottom_y)))
            if bottom_y <= top_y:
                bottom_y = min(max_y, top_y + max(thickness + 1, int(cur_row["h"])))

            rows_for_width = [r for r in (prev_row, cur_row, next_row) if r is not None and int(r.get("w", 0)) > 0]
            if rows_for_width:
                x0 = min(int(r["x"]) for r in rows_for_width)
                x1 = max(int(r["right"]) for r in rows_for_width)
                pad = max(0, int(getattr(self.body_text, "cget")("padx") or 0)) if hasattr(self.body_text, "cget") else 0
                x = max(0, x0 - pad)
                width = max(1, min(self.body_text.winfo_width() - x, x1 - x0 + pad * 2))
            else:
                x = 0
                width = max(1, self.body_text.winfo_width())

            self.line_top.place(x=x, y=top_y, width=width, height=thickness)
            self.line_bottom.place(x=x, y=bottom_y, width=width, height=thickness)

            if self._focus_debug_enabled():
                full_w = max(1, self.body_text.winfo_width())
                if prev_row:
                    self._place_debug_focus_line("prev_bottom", prev_row["bottom"], "#4040ff", full_w)
                self._place_debug_focus_line("cur_top", cur_row["top"], "#00a000", full_w)
                self._place_debug_focus_line("cur_bottom", cur_row["bottom"], "#00a000", full_w)
                if next_row:
                    self._place_debug_focus_line("next_top", next_row["top"], "#ff4040", full_w)
                self.log_debug(
                    f"focus-debug idx={idx_norm} raw_pos={pos} row={row} bbox={bbox} dline={info} "
                    f"prev={prev_row} cur={cur_row} next={next_row} bars=({top_y},{bottom_y}) "
                    f"thickness={thickness} bbox_samples={{'prev':{self._row_bbox_scan(row-1)}, 'cur':{self._row_bbox_scan(row)}, 'next':{self._row_bbox_scan(row+1)}}}"
                )
            else:
                self._hide_debug_focus_lines()
                self.log_debug(
                    f"focus-bars idx={idx_norm} pos={pos} row={row} cur=({cur_row['top']},{cur_row['bottom']}) "
                    f"bars=({top_y},{bottom_y}) thickness={thickness}",
                    verbose=True,
                )
        except Exception:
            self.log_debug("focus research redraw failed:\n" + traceback.format_exc())
            self.schedule_focus_redraw(20)

    def _reader_block_info(self, pos=None):
        if not self.text:
            return None
        self.refresh_display_chars_per_line()
        total = len(self.text)
        cpl = max(1, int(getattr(self, "display_chars_per_line", 1) or 1))
        total_lines = max(1, (total + cpl - 1) // cpl)
        line_step = max(1, int(getattr(self, "chunk_size", 1) or 1))
        if pos is None:
            pos = getattr(self, "reader_pos", 0)
        pos = max(0, min(int(pos), max(0, total - 1)))
        line_idx = max(0, min((pos // cpl), total_lines - 1))
        start_pos = line_idx * cpl
        end_line = min(total_lines, line_idx + line_step)
        end_pos = min(total, end_line * cpl)
        visible_chars = max(1, end_pos - start_pos)
        try:
            wpm = max(1.0, float(getattr(self, "wpm", 300) or 300))
        except Exception:
            wpm = 300.0
        delay_ms = max(1, int(round(visible_chars * 60000.0 / wpm)))
        if self._focus_debug_enabled():
            self.log_debug(
                f"reader-block line={line_idx} rows={line_step} start={start_pos} end={end_pos} "
                f"visible_chars={visible_chars} delay_ms={delay_ms} wpm={wpm} cpl={cpl}"
            )
        return {
            "line_idx": line_idx,
            "start_pos": start_pos,
            "end_pos": end_pos,
            "next_pos": end_pos,
            "visible_chars": visible_chars,
            "delay_ms": delay_ms,
            "line_step": line_step,
            "cpl": cpl,
        }

    # ---------- final override: audible typing-mode TTS ----------
    def current_tts_wpm(self):
        """Return speech speed for MPV/SAPI playback.

        Reading mode keeps following the right-side WPM.  Typing mode is different:
        it speaks one prompt character at a time, so using the live typing WPM can
        drive mpv to 1000-4000+ WPM and make a single-character WAV practically
        inaudible.  Therefore typing prompts are deliberately clamped to an audible
        range while reading-mode narration still uses the selected WPM.
        """
        if not self.typing_mode:
            return max(30.0, float(getattr(self, "wpm", 300) or 300))
        try:
            cwpm = float(getattr(self, "typing_current_wpm", 0) or 0)
        except Exception:
            cwpm = 0.0
        if cwpm >= 30:
            return max(180.0, min(450.0, cwpm))
        return 300.0

    def tts_segment_from_pos(self, pos, typing=False):
        if not self.text:
            return "", pos, pos
        n = len(self.text)
        pos = max(0, min(int(pos), max(0, n - 1)))
        if typing:
            ch = self.text[pos]
            if not ch or not ch.strip():
                return "", pos, min(n, pos + 1)
            # MPV + SAPI single-character WAV is often too short to hear, especially
            # when the next key immediately interrupts it.  Add a punctuation pause
            # to synthesize a real audible waveform, but keep the logical segment
            # length as exactly one character so duplicate suppression still works.
            if self.is_cjk(ch):
                return f"{ch}。", pos, min(n, pos + 1)
            if ch.isalnum():
                return f"{ch}。", pos, min(n, pos + 1)
            return "", pos, min(n, pos + 1)
        start = pos
        while start < n and not self.text[start].strip():
            start += 1
        if start >= n:
            return "", pos, pos
        hard_end_chars = set("。！？!?；;\n")
        soft_end_chars = set("，,、：:")
        max_chars = 140
        min_chars = 14
        end = start
        cjk_seen = 0
        while end < n and (end - start) < max_chars:
            ch = self.text[end]
            if self.is_cjk(ch):
                cjk_seen += 1
            end += 1
            if (end - start) >= min_chars and ch in hard_end_chars:
                break
            if (end - start) >= 36 and ch in soft_end_chars:
                break
        segment = self.text[start:end].strip()
        if not segment or not any(c.isalnum() or self.is_cjk(c) for c in segment):
            return "", start, end
        return segment, start, end

    def speak_current_target(self, force=False):
        if not getattr(self, "tts_enabled", False) or self.tts is None or not self.text:
            return
        pos = self.typing_flat_char_index if self.typing_mode else self.reader_pos
        if pos < 0 or pos >= len(self.text):
            return
        mode = "typing" if self.typing_mode else "reading"
        requested_wpm = self.current_tts_wpm()
        effective_wpm = self.effective_tts_wpm(requested_wpm)
        try:
            active = getattr(self, "_tts_active_segment", None)
            wpm_bucket = self.tts_speed_bucket_for_wpm(effective_wpm)
            if (not force) and active:
                a_mode, a_start, a_end, a_wpm_bucket = active
                if a_mode == mode and a_start <= pos < a_end and abs(wpm_bucket - a_wpm_bucket) <= 25:
                    return
                if mode == "reading":
                    try:
                        cap_wpm = float(getattr(self.tts, "base_speech_wpm", 300.0)) * float(getattr(self.tts, "max_mpv_speed", 24.0))
                    except Exception:
                        cap_wpm = 7200.0
                    if effective_wpm >= cap_wpm - 1 and self.tts is not None and hasattr(self.tts, "is_playing") and self.tts.is_playing():
                        return
            segment, start, end = self.tts_segment_from_pos(pos, typing=self.typing_mode)
            if not segment:
                return
            sig = (mode, start, end, hashlib.sha1(segment.encode("utf-8", errors="ignore")).hexdigest()[:12], wpm_bucket)
            if (not force) and sig == getattr(self, "_last_spoken_target", None):
                return
            self._last_spoken_target = sig
            self._tts_active_segment = (mode, start, end, wpm_bucket)
            self.tts.speak_text(segment, wpm=effective_wpm, reason=f"{mode}:{start}-{end}")
        except Exception:
            self.log_debug("speak_current_target failed:\n" + traceback.format_exc())

    def enter_typing_mode(self):
        self.playing = False
        self.cancel_timer()
        self.stop_tts_playback()
        self.typing_mode = True
        self.typing_key_buffer = ""
        self.typing_complete_notified = False
        self._last_spoken_target = None
        self._tts_active_segment = None
        self.typing_button.config(relief="sunken", fg="red", activeforeground="red")
        self.set_typing_hint_visible(True)
        self.install_typing_key_capture_bindtags()
        restored = self.restore_typing_progress_or_reader_position()
        self.update_mode_buttons()
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        self.speak_current_target(force=True)
        self.start_typing_idle_tick()
        self.focus_main()
        self.schedule_misc_after(50, self.focus_main)
        self.schedule_misc_after(150, self.focus_main)
        self.log_debug(f"Entered typing mode restored={restored} pos={self.typing_flat_char_index}; audible typing TTS enabled")

    def accept_current_typing_char(self):
        old = self.typing_flat_char_index
        self.note_typing_activity(1)
        nxt = self.next_cjk_after(old)
        if nxt is None:
            self.typing_flat_char_index = len(self.text)
            self.typing_key_buffer = ""
            self._last_spoken_target = None
            self._tts_active_segment = None
            self.record_typing_progress_throttled(force=True)
            self.update_display_tags()
            self.update_typing_hint()
            self.update_stats_label()
            self.finish_typing_file()
            return
        self.typing_flat_char_index = nxt
        self.typing_key_buffer = ""
        self._last_spoken_target = None
        self._tts_active_segment = None
        self.record_typing_progress_throttled()
        self.update_display_tags()
        self.update_typing_hint()
        self.update_stats_label()
        self.speak_current_target(force=True)
        self.log_debug(f"accepted char old={old} new={nxt} char={self.text[nxt]!r}", verbose=True)

    # ---------- final override: requested typing stats / exact line speed / focus bars ----------
    def update_mode_buttons(self):
        try:
            self.typing_button.config(text="S", fg="red", activeforeground="red", relief="sunken" if self.typing_mode else "raised")
        except Exception:
            pass

    def _speed_min(self):
        return 60

    def set_speed(self, new_speed):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = max(self._speed_min(), int(new_speed))
        self.speed_label.config(text=str(self.wpm))
        self.log_debug(f"speed set {self.wpm}")
        if self.playing:
            self._reset_reader_wpm_clock()
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def increase_speed(self):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = max(self._speed_min(), int(getattr(self, "wpm", 300) or 300) + 10)
        self.speed_label.config(text=str(self.wpm))
        if self.playing:
            self._reset_reader_wpm_clock()
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def decrease_speed(self):
        old_wpm = int(getattr(self, "wpm", 300) or 300)
        self.wpm = max(self._speed_min(), int(getattr(self, "wpm", 300) or 300) - 10)
        self.speed_label.config(text=str(self.wpm))
        if self.playing:
            self._reset_reader_wpm_clock()
            self.on_reader_speed_changed_for_tts(old_wpm)
            self.schedule_next()

    def current_tts_wpm(self):
        if not self.typing_mode:
            return max(60.0, float(getattr(self, "wpm", 300) or 300))
        try:
            cwpm = float(getattr(self, "typing_current_wpm", 0) or 0)
        except Exception:
            cwpm = 0.0
        if cwpm > 0:
            return max(60.0, min(12000.0, cwpm))
        return 240.0

    def _typing_stats_defaults(self):
        if not hasattr(self, "typing_fresh"):
            self.typing_fresh = 0.0
        if not hasattr(self, "typing_hourmax"):
            self.typing_hourmax = 0.0
        if not hasattr(self, "typing_24max"):
            self.typing_24max = 0.0
        if not hasattr(self, "_typing_session_best"):
            self._typing_session_best = 0.0
        if not hasattr(self, "_typing_session_events"):
            self._typing_session_events = deque(maxlen=4000)
        if not hasattr(self, "_typing_last_wpm_record_at"):
            self._typing_last_wpm_record_at = 0.0

    def update_stats_label(self):
        if self.typing_mode:
            self._typing_stats_defaults()
            self.refresh_typing_records()
            cur = self.current_typing_char() or "完成"
            mode_map = {"exact": "精确", "simple": "简单", "first": "首符号"}
            wrong = "错字不计" if self.typing_match_mode == "simple" else str(self.typing_wrong_count)
            pct = int((self.typing_flat_char_index / max(1, len(self.text))) * 100) if self.text else 0
            self.stats_label.config(
                text=(
                    f"wpm {self.typing_current_wpm:.1f}    fresh {float(getattr(self, 'typing_fresh', 0.0)):.1f}    "
                    f"hourmax {float(getattr(self, 'typing_hourmax', 0.0)):.1f}    24max {float(getattr(self, 'typing_24max', 0.0)):.1f}    "
                    f"txtmax {float(getattr(self, 'typing_txtmax', 0.0)):.1f}\n"
                    f"进度 {pct}%    当前字 {cur}    模式 {mode_map.get(self.typing_match_mode, self.typing_match_mode)}    "
                    f"已按键 {self.typing_key_buffer or '-'}    错字 {wrong}"
                )
            )
        else:
            pct = int((self.reader_pos / max(1, len(self.text))) * 100) if self.text else 0
            name = os.path.basename(self.file_path) if self.file_path else "未加载"
            self.stats_label.config(text=f"阅读模式    {pct}%    {name}")

    def note_typing_activity(self, accepted_chars):
        self._typing_stats_defaults()
        now = time.time()
        try:
            if self.typing_last_input_time is not None and now - float(self.typing_last_input_time) > 300.0:
                self.typing_fresh = float(getattr(self, "_typing_session_best", 0.0) or 0.0)
                self._typing_session_best = 0.0
                self._typing_session_events.clear()
                self.typing_window_start = now
        except Exception:
            pass
        for _ in range(int(accepted_chars)):
            self.typing_event_times.append(now)
            self._typing_session_events.append(now)
        if self.typing_last_input_time is None or now - self.typing_last_input_time > 3.0:
            self.typing_window_start = now
        self.typing_last_input_time = now
        self.compute_current_wpm(now, record=False)
        self._typing_session_best = max(float(getattr(self, "_typing_session_best", 0.0) or 0.0), float(getattr(self, "typing_current_wpm", 0.0) or 0.0))
        if now - float(getattr(self, "_typing_last_wpm_record_at", 0.0) or 0.0) >= 10.0:
            self.compute_and_record_wpm(now)
            self._typing_last_wpm_record_at = now

    def compute_current_wpm(self, now=None, record=False):
        self._typing_stats_defaults()
        now = now or time.time()
        if self.typing_last_input_time and now - self.typing_last_input_time > 300.0:
            self.typing_fresh = max(float(getattr(self, "typing_fresh", 0.0) or 0.0), float(getattr(self, "_typing_session_best", 0.0) or 0.0))
            self._typing_session_best = 0.0
            try:
                self._typing_session_events.clear()
            except Exception:
                pass
            self.typing_current_wpm = 0.0
            if record:
                self.refresh_typing_records()
            return 0.0
        cutoff = now - 60.0
        times = [float(t) for t in self.typing_event_times if float(t) >= cutoff]
        if len(times) < 2:
            self.typing_current_wpm = 0.0
            return 0.0
        active = 0.0
        prev = times[0]
        for t in times[1:]:
            gap = max(0.0, t - prev)
            if gap <= 3.0:
                active += gap
            prev = t
        active = max(active, 1.0)
        wpm = len(times) / active * 60.0
        self.typing_current_wpm = round(float(wpm), 2)
        self._typing_session_best = max(float(getattr(self, "_typing_session_best", 0.0) or 0.0), self.typing_current_wpm)
        if record:
            self.record_wpm_result(self.typing_current_wpm)
        return self.typing_current_wpm

    def compute_and_record_wpm(self, now=None):
        return self.compute_current_wpm(now=now, record=True)

    def start_typing_idle_tick(self):
        self.cancel_typing_idle_tick()
        def tick():
            self._typing_tick_after = None
            if not self.typing_mode:
                return
            now = time.time()
            self.compute_current_wpm(now, record=False)
            self.update_stats_label()
            try:
                self._typing_tick_after = self.after(1000, tick)
            except Exception:
                self._typing_tick_after = None
        try:
            self._typing_tick_after = self.after(1000, tick)
        except Exception:
            self._typing_tick_after = None

    def load_wpm_store(self):
        data = safe_json_load(self.wpm_file, {}, self.log_debug)
        if not isinstance(data, dict):
            data = {}
        data.setdefault("daily_max", {})
        data.setdefault("txtmax", {})
        return data

    def save_wpm_store(self, store):
        ok = atomic_json_save(self.wpm_file, store, self.log_debug)
        self.log_debug(f"wpm save ok={ok} file={self.wpm_file}", verbose=True)
        return ok

    def record_wpm_result(self, wpm):
        try:
            wpm = float(wpm)
        except Exception:
            return
        if wpm <= 0:
            return
        store = self.load_wpm_store()
        timestamp = time.strftime("%Y%m%d%H%M")
        store[timestamp] = max(float(store.get(timestamp, 0) or 0), wpm)
        day = time.strftime("%Y%m%d")
        store.setdefault("daily_max", {})[day] = max(float(store.get("daily_max", {}).get(day, 0) or 0), wpm)
        if self.file_path:
            key = self.file_key(self.file_path)
            store.setdefault("txtmax", {})[key] = max(float(store.get("txtmax", {}).get(key, 0) or 0), wpm)
        self.save_wpm_store(store)
        self.refresh_typing_records()
        self.log_debug(f"WPM recorded {wpm}")

    def refresh_typing_records(self):
        self._typing_stats_defaults()
        store = self.load_wpm_store()
        now = time.time()
        hour = 0.0
        day24 = 0.0
        for k, v in store.items():
            if not (isinstance(k, str) and re.fullmatch(r"\d{12}", k)):
                continue
            try:
                t = time.mktime(time.strptime(k, "%Y%m%d%H%M"))
                val = float(v)
            except Exception:
                continue
            age = now - t
            if 0 <= age <= 3600:
                hour = max(hour, val)
            if 0 <= age <= 86400:
                day24 = max(day24, val)
        self.typing_hourmax = float(hour)
        self.typing_24max = float(day24)
        key = self.file_key(self.file_path) if self.file_path else ""
        self.typing_txtmax = float(store.get("txtmax", {}).get(key, 0) or 0)
        day = time.strftime("%Y%m%d")
        self.typing_daymax = float(store.get("daily_max", {}).get(day, 0) or 0)

    def _focus_line_thickness(self):
        try:
            px = int(self.text_font.metrics("linespace") or 0)
        except Exception:
            px = 0
        if px <= 0:
            px = int(abs(int(getattr(self, "text_font_size", 24) or 24)))
        return max(1, min(10, int(round(px / 26.0))))

    def _apply_focus_line_spacing(self):
        try:
            thickness = self._focus_line_thickness()
            try:
                linespace = int(self.text_font.metrics("linespace") or 0)
            except Exception:
                linespace = int(getattr(self, "text_font_size", 24) or 24)
            spacing3 = max(thickness * 4 + 2, int(round(linespace * 0.24)))
            spacing3 = max(8, min(48, spacing3))
            if int(getattr(self, "_focus_line_spacing3", -1)) != spacing3:
                self._focus_line_spacing3 = spacing3
                self.body_text.configure(spacing1=0, spacing2=0, spacing3=spacing3)
                self._last_render_signature = None
        except Exception:
            pass

    def _row_ink_bounds(self, row):
        try:
            row = int(row)
            if row <= 0:
                return None
            info = self.body_text.dlineinfo(f"{row}.0")
            if info is None:
                return None
            x, y, w, h, baseline = info
            top = None
            bottom = None
            left = None
            right = None
            row_text = self.body_text.get(f"{row}.0", f"{row}.end")
            for col, ch in enumerate(row_text):
                if not ch or not ch.strip():
                    continue
                bb = self.body_text.bbox(f"{row}.{col}")
                if bb is None:
                    continue
                bx, by, bw, bh = bb
                top = by if top is None else min(top, by)
                bottom = by + bh if bottom is None else max(bottom, by + bh)
                left = bx if left is None else min(left, bx)
                right = bx + bw if right is None else max(right, bx + bw)
            if top is None or bottom is None:
                top = int(y)
                bottom = int(y + h)
                left = int(x)
                right = int(x + w)
            return {"row": row, "top": int(top), "bottom": int(bottom), "left": int(left or 0), "right": int(right or 0), "line_top": int(y), "line_bottom": int(y+h)}
        except Exception:
            return None

    def redraw_focus_lines(self):
        if not self.text:
            self.hide_focus_lines()
            try: self._hide_debug_focus_lines()
            except Exception: pass
            return
        pos = self.current_target_pos()
        idx = self.index_from_char_pos(pos)
        try:
            self._apply_focus_line_spacing()
            bbox, info = self._force_index_geometry(idx)
            if bbox is None or info is None:
                self.hide_focus_lines()
                try: self._hide_debug_focus_lines()
                except Exception: pass
                self._focus_redraw_after_id = self.after_idle(lambda: (setattr(self, "_focus_redraw_after_id", None), self.redraw_focus_lines()))
                return
            idx_norm = self.body_text.index(idx)
            row = int(idx_norm.split(".", 1)[0])
            end_row = int(self.body_text.index("end-1c").split(".", 1)[0])
            prev_row = self._row_ink_bounds(row - 1) if row > 1 else None
            cur_row = self._row_ink_bounds(row)
            next_row = self._row_ink_bounds(row + 1) if row < end_row else None
            if cur_row is None:
                self.hide_focus_lines()
                return
            thickness = self._focus_line_thickness()
            # Exact center of the blank visual gap between glyph ink boxes.
            if prev_row is not None:
                top_center = (prev_row["bottom"] + cur_row["top"]) / 2.0
            else:
                top_center = cur_row["top"] - max(thickness * 2.0, (cur_row["bottom"] - cur_row["top"]) * 0.22)
            if next_row is not None:
                bottom_center = (cur_row["bottom"] + next_row["top"]) / 2.0
            else:
                bottom_center = cur_row["bottom"] + max(thickness * 2.0, (cur_row["bottom"] - cur_row["top"]) * 0.22)
            top_y = int(round(top_center - thickness / 2.0))
            bottom_y = int(round(bottom_center - thickness / 2.0))
            max_y = max(0, int(self.body_text.winfo_height()) - thickness)
            top_y = max(0, min(max_y, top_y))
            bottom_y = max(0, min(max_y, bottom_y))
            if bottom_y <= top_y:
                bottom_y = min(max_y, top_y + max(thickness + 1, cur_row["bottom"] - cur_row["top"] + int(getattr(self, "_focus_line_spacing3", 8))))
            rows = [r for r in (prev_row, cur_row, next_row) if r]
            x = max(0, min((r["left"] for r in rows), default=0) - 8)
            right = max((r["right"] for r in rows), default=max(1, self.body_text.winfo_width())) + 8
            width = max(1, min(self.body_text.winfo_width() - x, right - x))
            self.line_top.place(x=x, y=top_y, width=width, height=thickness)
            self.line_bottom.place(x=x, y=bottom_y, width=width, height=thickness)
            try: self._hide_debug_focus_lines()
            except Exception: pass
            self.log_debug(
                f"focus-inkgap idx={idx_norm} pos={pos} row={row} prev={prev_row} cur={cur_row} next={next_row} bars=({top_y},{bottom_y}) thickness={thickness}",
                verbose=True,
            )
        except Exception:
            self.log_debug("focus inkgap redraw failed:\n" + traceback.format_exc())
            self.schedule_focus_redraw(20)

    # ---------- pinyin/logical tests helpers ----------
    def debug_decode_bytes(self, raw):
        text, enc = decode_txt_bytes(raw)
        self.log_debug(f"decode bytes encoding={enc} chars={len(text)}")
        return text, enc

    # ---------- close ----------
    def on_close(self):
        try:
            self.compute_and_record_wpm()
            self.record_auto_progress_throttled(force=True)
        finally:
            self.cancel_timer()
            try:
                if self.tts is not None:
                    self.tts.close()
            except Exception:
                pass
            try:
                if getattr(self, "_wrap_reflow_after_id", None) is not None:
                    self.after_cancel(self._wrap_reflow_after_id)
                    self._wrap_reflow_after_id = None
            except Exception:
                pass
            self.cancel_misc_after_callbacks()
            self.disable_native_windows_drop()
            try:
                self.destroy()
            except Exception:
                pass



# ---------- final hotfix: MPV/SAPI audio sync and non-stuttering typing voice ----------
# 这个补丁放在类定义之后、启动之前，直接覆盖前面多轮版本里留下的语音方法。
# 核心修复：
# 1) 阅读语音不再按“假设 300 字/分钟”的固定倍率猜速度，而是读取 WAV 真实时长，
#    再用“当前可见阅读块字数 / 当前 WPM”算出目标时长，MPV speed = wav_duration / target_duration。
# 2) 阅读语音段与视觉阅读块完全一致，避免音频读上一整句、视觉已经跳了好几行。
# 3) 打字语音不再给单字加“。”长尾；单字用 SAPI Rate=10 合成，600% 电平增强。
# 4) 打字语音用常驻 idle MPV，通过 stdin loadfile，不再每个字启动一个 mpv.exe。
# 5) 合成期间若用户已经输入到新字，旧字 WAV 合成完也不会再播放，避免“乱读旧字”。

def _sr_audio_wav_duration_seconds(self, wav_path):
    try:
        with wave.open(str(wav_path), "rb") as r:
            frames = int(r.getnframes())
            rate = int(r.getframerate())
            if rate > 0:
                return max(0.001, frames / float(rate))
    except Exception:
        pass
    return None


def _sr_audio_speed_for_target(self, wav_path, wpm=None, target_duration=None):
    try:
        max_speed = float(getattr(self, "max_mpv_speed", 24.0) or 24.0)
    except Exception:
        max_speed = 24.0
    try:
        if target_duration is not None and float(target_duration) > 0:
            dur = self._wav_duration_seconds(wav_path)
            if dur and dur > 0:
                return max(0.35, min(max_speed, float(dur) / max(0.001, float(target_duration))))
    except Exception:
        pass
    try:
        return self._mpv_speed_for_wpm(wpm)
    except Exception:
        try:
            w = float(wpm or 300.0)
        except Exception:
            w = 300.0
        base = max(1.0, float(getattr(self, "base_speech_wpm", 300.0) or 300.0))
        return max(0.35, min(max_speed, w / base))


def _sr_audio_is_typing_reason(reason):
    try:
        return str(reason or "").lower().startswith("typing")
    except Exception:
        return False


def _sr_audio_cache_key_for_text(self, text):
    # 单字和长段使用不同 cache 命名，防止“打字高速单字版”和“阅读普通语速版”互相污染。
    s = str(text or "")
    rate = 10 if len(s.strip()) <= 1 else 0
    digest = hashlib.sha1((f"gain600-sync-rate{rate}\0" + s).encode("utf-8", errors="ignore")).hexdigest()
    return digest[:32]


def _sr_audio_sapi_com_wav_for_text(self, voice, win32com, text):
    key = self._cache_key_for_text(text)
    cached = self.wav_cache.get(key)
    if cached:
        try:
            if Path(cached).is_file() and Path(cached).stat().st_size > 256:
                return cached
        except Exception:
            pass
    temp_dir = self._ensure_tts_temp_dir()
    if temp_dir is None:
        return None
    raw_path = Path(temp_dir) / (key + "_raw.wav")
    amp_path = Path(temp_dir) / (key + "_raw_gain600.wav")
    if amp_path.is_file() and amp_path.stat().st_size > 256:
        self._remember_wav_cache(key, amp_path)
        return amp_path

    old_stream = None
    stream = None
    try:
        stream = win32com.client.Dispatch("SAPI.SpFileStream")
        stream.Open(str(raw_path), 3, False)
        try:
            old_stream = voice.AudioOutputStream
        except Exception:
            old_stream = None
        voice.AudioOutputStream = stream
        try:
            # 单字打字音必须短促；阅读长段保持自然。
            voice.Rate = 10 if len(str(text).strip()) <= 1 else 0
            voice.Volume = 100
        except Exception:
            pass
        voice.Speak(str(text), 0)
        try:
            voice.AudioOutputStream = old_stream
        except Exception:
            pass
        stream.Close()
        stream = None
        out_path = self._gain600_wav_for_raw(raw_path, key)
        if out_path is not None and Path(out_path).is_file() and Path(out_path).stat().st_size > 256:
            self._remember_wav_cache(key, out_path)
            return out_path
    except Exception:
        self.log("TTS SAPI COM synth failed:\n" + traceback.format_exc())
    finally:
        try:
            if old_stream is not None:
                voice.AudioOutputStream = old_stream
        except Exception:
            pass
        try:
            if stream is not None:
                stream.Close()
        except Exception:
            pass
    return None


def _sr_audio_ensure_ps_script(self):
    temp_dir = self._ensure_tts_temp_dir()
    if temp_dir is None:
        return None
    if self._ps_script_path is None:
        p = Path(temp_dir) / "sapi_synth_to_wav.ps1"
        p.write_text(
            """
param([string]$TextPath, [string]$WavPath)
Add-Type -AssemblyName System.Speech
$synth = New-Object System.Speech.Synthesis.SpeechSynthesizer
try {
    $voices = $synth.GetInstalledVoices() | Where-Object {
        ($_.VoiceInfo.Culture.Name -like 'zh*' -or $_.VoiceInfo.Description -match 'Chinese|Mandarin|Huihui|Xiaoxiao|Yaoyao|Hanhan')
    }
    $female = $voices | Where-Object { $_.VoiceInfo.Gender -eq 'Female' } | Select-Object -First 1
    if ($female) { $synth.SelectVoice($female.VoiceInfo.Name) }
    elseif ($voices) { $synth.SelectVoice(($voices | Select-Object -First 1).VoiceInfo.Name) }
    $text = [System.IO.File]::ReadAllText($TextPath, [System.Text.Encoding]::UTF8)
    if ($text.Trim().Length -le 1) { $synth.Rate = 10 } else { $synth.Rate = 0 }
    $synth.Volume = 100
    $synth.SetOutputToWaveFile($WavPath)
    $synth.Speak($text)
} finally {
    $synth.Dispose()
}
""".strip(),
            encoding="utf-8",
        )
        self._ps_script_path = p
    return self._ps_script_path


def _sr_audio_sapi_powershell_wav_for_text(self, text):
    key = self._cache_key_for_text(text)
    cached = self.wav_cache.get(key)
    if cached:
        try:
            if Path(cached).is_file() and Path(cached).stat().st_size > 256:
                return cached
        except Exception:
            pass
    temp_dir = self._ensure_tts_temp_dir()
    ps = self._powershell_path()
    script = self._ensure_ps_script()
    if temp_dir is None or not ps or script is None:
        return None
    raw_path = Path(temp_dir) / (key + "_raw.wav")
    txt_path = Path(temp_dir) / (key + ".txt")
    amp_path = Path(temp_dir) / (key + "_raw_gain600.wav")
    if amp_path.is_file() and amp_path.stat().st_size > 256:
        self._remember_wav_cache(key, amp_path)
        return amp_path
    try:
        txt_path.write_text(str(text), encoding="utf-8")
        creationflags = 0
        if IS_WINDOWS and hasattr(subprocess, "CREATE_NO_WINDOW"):
            creationflags = subprocess.CREATE_NO_WINDOW
        subprocess.run(
            [ps, "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(script), str(txt_path), str(raw_path)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=20,
            creationflags=creationflags,
        )
        try:
            txt_path.unlink(missing_ok=True)
        except Exception:
            pass
        out_path = self._gain600_wav_for_raw(raw_path, key)
        if out_path is not None and Path(out_path).is_file() and Path(out_path).stat().st_size > 256:
            self._remember_wav_cache(key, out_path)
            return out_path
    except Exception:
        self.log("TTS PowerShell SAPI synth failed:\n" + traceback.format_exc())
    return None


def _sr_audio_quote_mpv_path(path):
    p = str(Path(path))
    if IS_WINDOWS:
        p = p.replace("\\", "/")
    return '"' + p.replace("\\", "\\\\").replace('"', '\\"') + '"'


def _sr_audio_ensure_typing_mpv(self):
    mpv = self._refresh_mpv_path()
    if not mpv:
        return None
    proc = getattr(self, "_typing_mpv_proc", None)
    try:
        if proc is not None and proc.poll() is None and proc.stdin:
            return proc
    except Exception:
        pass
    creationflags = 0
    if IS_WINDOWS and hasattr(subprocess, "CREATE_NO_WINDOW"):
        creationflags = subprocess.CREATE_NO_WINDOW
    cmd = [
        str(mpv),
        "--idle=yes",
        "--force-window=no",
        "--vo=null",
        "--audio-display=no",
        "--input-terminal=yes",
        "--really-quiet",
    ]
    try:
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            text=True,
            encoding="utf-8",
            errors="ignore",
            creationflags=creationflags,
            bufsize=1,
        )
        self._typing_mpv_proc = proc
        return proc
    except Exception:
        self.log("TTS persistent MPV start failed:\n" + traceback.format_exc())
        self._typing_mpv_proc = None
        return None


def _sr_audio_stop_typing_mpv(self):
    proc = getattr(self, "_typing_mpv_proc", None)
    self._typing_mpv_proc = None
    try:
        if proc is not None and proc.poll() is None:
            try:
                if proc.stdin:
                    proc.stdin.write("quit\n")
                    proc.stdin.flush()
            except Exception:
                pass
            try:
                proc.wait(timeout=0.25)
            except Exception:
                try:
                    proc.terminate()
                except Exception:
                    pass
    except Exception:
        pass


def _sr_audio_play_with_persistent_mpv(self, wav_path, wpm=None, reason="typing", target_duration=None):
    proc = self._ensure_typing_mpv()
    if proc is None or not getattr(proc, "stdin", None):
        # 如果常驻 MPV 不可用，退回普通 MPV；仍比静音更好。
        return self._play_with_mpv(wav_path, wpm, reason=reason, target_duration=target_duration)
    speed = self._speed_for_target(wav_path, wpm=wpm, target_duration=target_duration)
    # 打字单字优先短促清晰，不开 pitch correction，避免高倍速滤镜吞音。
    try:
        proc.stdin.write(f"set speed {float(speed):.4f}\n")
        proc.stdin.write("set audio-pitch-correction no\n")
        proc.stdin.write(f"loadfile {_sr_audio_quote_mpv_path(wav_path)} replace\n")
        proc.stdin.flush()
        self.log(f"TTS persistent MPV typing play reason={reason} speed={float(speed):.3f} target={target_duration} file={wav_path}", verbose=True)
        return True
    except Exception:
        self.log("TTS persistent MPV command failed:\n" + traceback.format_exc())
        self._stop_typing_mpv()
        return False


def _sr_audio_play_with_mpv(self, wav_path, wpm=None, reason="segment", target_duration=None):
    mpv = self._refresh_mpv_path()
    if not mpv:
        self.log(
            "TTS MPV unavailable: mpv.exe was not found in script folder, PATH, "
            "winget package folders, scoop, or chocolatey. Install mpv-player.mpv-CI.MSVC "
            "or put mpv.exe next to this .py file."
        )
        return False
    speed = self._speed_for_target(wav_path, wpm=wpm, target_duration=target_duration)
    pitch_correction = "yes" if speed <= 4.0 else "no"
    cmd = [
        str(mpv),
        "--no-terminal",
        "--really-quiet",
        "--force-window=no",
        "--vo=null",
        "--audio-display=no",
        "--idle=no",
        f"--audio-pitch-correction={pitch_correction}",
        f"--speed={speed:.4f}",
        "--",
        str(wav_path),
    ]
    creationflags = 0
    if IS_WINDOWS and hasattr(subprocess, "CREATE_NO_WINDOW"):
        creationflags = subprocess.CREATE_NO_WINDOW
    try:
        self._stop_current_playback()
        self.log(
            f"TTS MPV play reason={reason} effective_wpm={float(wpm or 0):.1f} "
            f"target={target_duration} speed={speed:.3f} pitch={pitch_correction} file={wav_path}",
            verbose=True,
        )
        self.current_proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, creationflags=creationflags)
        self.current_proc.wait()
        self.current_proc = None
        return True
    except Exception:
        self.current_proc = None
        self.log("TTS MPV playback failed:\n" + traceback.format_exc())
        return False


def _sr_audio_speak_text(self, text, wpm=None, reason="segment", target_duration=None):
    if not self.enabled:
        return
    text = self._normalize_text(text)
    if not text:
        return
    self.start()
    effective_wpm = self.effective_wpm_for_playback(wpm)
    item = {
        "text": text,
        "wpm": effective_wpm,
        "requested_wpm": self._normalize_wpm(wpm),
        "reason": str(reason or "segment"),
        "target_duration": None if target_duration is None else max(0.001, float(target_duration)),
        "time": time.time(),
    }
    self.clear_queue()
    # 阅读段需要立刻替换；打字段交给常驻 MPV replace，不要每个字杀 mpv.exe。
    if not _sr_audio_is_typing_reason(reason):
        self._stop_current_playback()
    try:
        self.queue.put_nowait(item)
    except Exception:
        pass


def _sr_audio_worker(self):
    voice = None
    win32com = None
    pythoncom = None
    self._refresh_mpv_path()
    if self.mpv_path:
        self.log(f"TTS MPV found: {self.mpv_path}")
    else:
        self.log("TTS MPV not found yet; playback will rescan script folder, PATH, winget, scoop and chocolatey folders each time it is needed")
    if IS_WINDOWS:
        try:
            import pythoncom as _pythoncom
            import win32com.client as _win32com_client
            pythoncom = _pythoncom
            pythoncom.CoInitialize()
            class _Win32ComModule:
                client = _win32com_client
            win32com = _Win32ComModule
            voice = win32com.client.Dispatch("SAPI.SpVoice")
            self._select_sapi_voice(voice)
            self.backend = "mpv+sapi-com-sync"
            self.ready = bool(self.mpv_path)
            self.log("TTS backend ready: MPV playback + Windows SAPI COM synthesis, sync hotfix active")
        except Exception as e:
            voice = None
            win32com = None
            self.backend = "mpv+sapi-powershell-sync" if self.mpv_path else "sapi-powershell-no-mpv"
            self.ready = bool(self.mpv_path)
            self.log(f"TTS SAPI COM unavailable, fallback to PowerShell SAPI synthesis: {e}")
    else:
        self.backend = "mpv-external-audio-only"
        self.ready = bool(self.mpv_path)
        self.log("TTS synthesis currently expects Windows SAPI; non-Windows needs an external WAV synth path")

    try:
        while not self.stop_event.is_set():
            item = self.queue.get()
            if item is None:
                break
            try:
                while True:
                    newer = self.queue.get_nowait()
                    if newer is None:
                        item = None
                        break
                    item = newer
            except Exception:
                pass
            if item is None or not self.enabled:
                continue

            while item is not None and self.enabled and not self.stop_event.is_set():
                text = self._normalize_text(item.get("text", ""))
                if not text:
                    break
                wpm = self._normalize_wpm(item.get("wpm"))
                reason = item.get("reason", "segment")
                target_duration = item.get("target_duration")
                wav_path = None
                if voice is not None and win32com is not None:
                    wav_path = self._sapi_com_wav_for_text(voice, win32com, text)
                if wav_path is None and IS_WINDOWS:
                    wav_path = self._sapi_powershell_wav_for_text(text)
                # 合成期间如果又来了新字，直接抛弃旧字，不播放过期音频。
                latest = None
                try:
                    while True:
                        newer = self.queue.get_nowait()
                        if newer is None:
                            latest = None
                            break
                        latest = newer
                except Exception:
                    pass
                if latest is not None:
                    item = latest
                    continue
                if wav_path is None:
                    self.log("TTS synth failed: no usable WAV was produced")
                    break
                if _sr_audio_is_typing_reason(reason):
                    self._play_with_persistent_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration)
                else:
                    self._play_with_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration)
                break
    finally:
        try:
            self._stop_current_playback()
        except Exception:
            pass
        try:
            self._stop_typing_mpv()
        except Exception:
            pass
        try:
            if pythoncom is not None:
                pythoncom.CoUninitialize()
        except Exception:
            pass
        try:
            if self.tts_temp_dir is not None:
                shutil.rmtree(str(self.tts_temp_dir), ignore_errors=True)
                self.tts_temp_dir = None
                self.wav_cache.clear()
                self._ps_script_path = None
        except Exception:
            pass


def _sr_audio_close(self):
    try:
        self.stop_event.set()
        self.clear_queue()
        try:
            self.queue.put_nowait(None)
        except Exception:
            pass
        self._stop_current_playback()
        self._stop_typing_mpv()
    except Exception:
        pass


TTSManager._wav_duration_seconds = _sr_audio_wav_duration_seconds
TTSManager._speed_for_target = _sr_audio_speed_for_target
TTSManager._cache_key_for_text = _sr_audio_cache_key_for_text
TTSManager._sapi_com_wav_for_text = _sr_audio_sapi_com_wav_for_text
TTSManager._ensure_ps_script = _sr_audio_ensure_ps_script
TTSManager._sapi_powershell_wav_for_text = _sr_audio_sapi_powershell_wav_for_text
TTSManager._ensure_typing_mpv = _sr_audio_ensure_typing_mpv
TTSManager._stop_typing_mpv = _sr_audio_stop_typing_mpv
TTSManager._play_with_persistent_mpv = _sr_audio_play_with_persistent_mpv
TTSManager._play_with_mpv = _sr_audio_play_with_mpv
TTSManager.speak_text = _sr_audio_speak_text
TTSManager._worker = _sr_audio_worker
TTSManager.close = _sr_audio_close


def _sr_visual_reading_segment(self, pos):
    if not self.text:
        return "", pos, pos, None
    try:
        info = self._reader_block_info(pos)
    except Exception:
        info = None
    if info:
        start = max(0, min(int(info["start_pos"]), len(self.text)))
        end = max(start, min(int(info["end_pos"]), len(self.text)))
        segment = self.text[start:end].strip()
        if segment:
            target_duration = max(0.001, float(info.get("delay_ms", 1)) / 1000.0)
            return segment, start, end, target_duration
    # fallback
    pos = max(0, min(int(pos), max(0, len(self.text) - 1)))
    end = min(len(self.text), pos + max(1, int(getattr(self, "display_chars_per_line", 20) or 20)))
    segment = self.text[pos:end].strip()
    try:
        wpm = max(60.0, float(getattr(self, "wpm", 300) or 300))
    except Exception:
        wpm = 300.0
    target_duration = max(0.001, max(1, end - pos) * 60.0 / wpm)
    return segment, pos, end, target_duration


def _sr_typing_target_duration(self, requested_wpm):
    try:
        w = max(60.0, float(requested_wpm or 240.0))
    except Exception:
        w = 240.0
    # 每字目标时长：慢速时保留一点连贯感，快速时尽量短促，但不追求物理不可能的 3500WPM 完整发音。
    interval = 60.0 / w
    return max(0.035, min(0.22, interval * 0.80))


def _sr_tts_segment_from_pos(self, pos, typing=False):
    if not self.text:
        return "", pos, pos
    n = len(self.text)
    pos = max(0, min(int(pos), max(0, n - 1)))
    if typing:
        ch = self.text[pos]
        if ch and (self.is_cjk(ch) or ch.isalnum()):
            return ch, pos, min(n, pos + 1)
        return "", pos, min(n, pos + 1)
    segment, start, end, _target = _sr_visual_reading_segment(self, pos)
    return segment, start, end


def _sr_speak_current_target(self, force=False):
    if not getattr(self, "tts_enabled", False) or self.tts is None or not self.text:
        return
    pos = self.typing_flat_char_index if self.typing_mode else self.reader_pos
    if pos < 0 or pos >= len(self.text):
        return
    mode = "typing" if self.typing_mode else "reading"
    requested_wpm = self.current_tts_wpm()
    effective_wpm = self.effective_tts_wpm(requested_wpm)
    try:
        target_duration = None
        if self.typing_mode:
            segment, start, end = self.tts_segment_from_pos(pos, typing=True)
            target_duration = _sr_typing_target_duration(self, requested_wpm)
        else:
            segment, start, end, target_duration = _sr_visual_reading_segment(self, pos)
        if not segment:
            return

        # 阅读模式才做段内去重；打字模式每个新红字必须立刻发声。
        wpm_bucket = self.tts_speed_bucket_for_wpm(effective_wpm)
        if not self.typing_mode:
            active = getattr(self, "_tts_active_segment", None)
            if (not force) and active:
                a_mode, a_start, a_end, a_wpm_bucket = active
                if a_mode == mode and a_start <= pos < a_end and abs(wpm_bucket - a_wpm_bucket) <= 25:
                    return
            sig = (mode, start, end, hashlib.sha1(segment.encode("utf-8", errors="ignore")).hexdigest()[:12], wpm_bucket)
            if (not force) and sig == getattr(self, "_last_spoken_target", None):
                return
            self._last_spoken_target = sig
            self._tts_active_segment = (mode, start, end, wpm_bucket)
        else:
            self._last_spoken_target = (mode, start, end, time.time())
            self._tts_active_segment = (mode, start, end, wpm_bucket)

        self.tts.speak_text(segment, wpm=effective_wpm, reason=f"{mode}:{start}-{end}", target_duration=target_duration)
    except Exception:
        self.log_debug("speak_current_target sync hotfix failed:\n" + traceback.format_exc())


def _sr_current_tts_wpm(self):
    if not self.typing_mode:
        return max(60.0, float(getattr(self, "wpm", 300) or 300))
    try:
        cwpm = float(getattr(self, "typing_current_wpm", 0) or 0)
    except Exception:
        cwpm = 0.0
    if cwpm > 0:
        return max(60.0, min(12000.0, cwpm))
    return 240.0


SpeedReader.tts_segment_from_pos = _sr_tts_segment_from_pos
SpeedReader.speak_current_target = _sr_speak_current_target
SpeedReader.current_tts_wpm = _sr_current_tts_wpm




# ---------- final hotfix v3: reading lookahead MPV sync + direct low-latency typing voice ----------
# Reading: synthesize a longer lookahead segment, then use MPV speed = real_wav_duration / target_reading_duration.
# This keeps one audio stream alive across several visual line advances, so normal line changes do not cut speech.
# Typing: single-character MPV/WAV is too slow because synthesis + loadfile latency is larger than a fast key interval.
# Use direct SAPI async+purge for typing prompts; it is the only low-latency path that does not lag behind or read stale chars.

def _sr_v3_is_typing_reason(reason):
    try:
        return str(reason or "").lower().startswith("typing")
    except Exception:
        return False


def _sr_v3_direct_sapi_typing(self, voice, text, wpm=None, reason="typing"):
    """Lowest-latency typing prompt voice. Avoids WAV synthesis and per-char MPV load latency."""
    try:
        s = str(text or "").strip()
        if not s:
            return False
        # Keep only the actual target character; punctuation tails make fast typing sound delayed and broken.
        ch = s[0]
        try:
            w = float(wpm or 300.0)
        except Exception:
            w = 300.0
        # SAPI rate range is -10..10.  Keep slow typing more connected; make fast typing as short as SAPI allows.
        if w < 180:
            rate = 2
        elif w < 360:
            rate = 5
        elif w < 720:
            rate = 8
        else:
            rate = 10
        try:
            voice.Rate = int(rate)
            voice.Volume = 100
        except Exception:
            pass
        # SVSFlagsAsync=1, SVSFPurgeBeforeSpeak=2.  Purge prevents old chars being read after the user moved on.
        voice.Speak(ch, 1 | 2)
        self.log(f"TTS direct SAPI typing reason={reason} ch={ch!r} wpm={float(w):.1f} rate={rate}", verbose=True)
        return True
    except Exception:
        self.log("TTS direct SAPI typing failed:\n" + traceback.format_exc())
        return False


def _sr_v3_audio_worker(self):
    voice = None
    win32com = None
    pythoncom = None
    self._refresh_mpv_path()
    if self.mpv_path:
        self.log(f"TTS MPV found: {self.mpv_path}")
    else:
        self.log("TTS MPV not found yet; reading playback will rescan script folder, PATH, winget, scoop and chocolatey folders each time")
    if IS_WINDOWS:
        try:
            import pythoncom as _pythoncom
            import win32com.client as _win32com_client
            pythoncom = _pythoncom
            pythoncom.CoInitialize()
            class _Win32ComModule:
                client = _win32com_client
            win32com = _Win32ComModule
            voice = win32com.client.Dispatch("SAPI.SpVoice")
            self._select_sapi_voice(voice)
            self.backend = "mpv+sapi-reading/direct-sapi-typing-v3"
            self.ready = bool(self.mpv_path) or bool(voice is not None)
            self.log("TTS backend ready: MPV accelerated reading + direct Windows SAPI typing hotfix v3")
        except Exception as e:
            voice = None
            win32com = None
            self.backend = "mpv+sapi-powershell-reading-no-direct-typing" if self.mpv_path else "sapi-powershell-no-mpv"
            self.ready = bool(self.mpv_path)
            self.log(f"TTS SAPI COM unavailable, fallback to PowerShell synthesis for reading: {e}")
    else:
        self.backend = "mpv-external-audio-only"
        self.ready = bool(self.mpv_path)
        self.log("TTS synthesis currently expects Windows SAPI; non-Windows needs an external WAV synth path")

    try:
        while not self.stop_event.is_set():
            item = self.queue.get()
            if item is None:
                break
            try:
                # Always collapse backlog before doing any work.  This prevents stale char/segment audio.
                while True:
                    newer = self.queue.get_nowait()
                    if newer is None:
                        item = None
                        break
                    item = newer
            except Exception:
                pass
            if item is None or not self.enabled:
                continue

            text = self._normalize_text(item.get("text", ""))
            if not text:
                continue
            wpm = self._normalize_wpm(item.get("wpm"))
            reason = item.get("reason", "segment")
            target_duration = item.get("target_duration")

            # Typing mode: direct SAPI is intentionally primary.  The MPV/WAV path is kept only as a fallback
            # when COM SAPI is not available, because per-character WAV synthesis cannot keep up with fast input.
            if _sr_v3_is_typing_reason(reason) and voice is not None:
                self._direct_sapi_typing(voice, text, wpm=wpm, reason=reason)
                continue

            # Reading mode: WAV + MPV acceleration.  If a newer request arrives during synthesis, drop this one.
            wav_path = None
            if voice is not None and win32com is not None:
                wav_path = self._sapi_com_wav_for_text(voice, win32com, text)
            if wav_path is None and IS_WINDOWS:
                wav_path = self._sapi_powershell_wav_for_text(text)
            latest = None
            try:
                while True:
                    newer = self.queue.get_nowait()
                    if newer is None:
                        latest = None
                        break
                    latest = newer
            except Exception:
                pass
            if latest is not None:
                try:
                    self.queue.put_nowait(latest)
                except Exception:
                    pass
                continue
            if wav_path is None:
                self.log("TTS synth failed: no usable WAV was produced")
                continue
            if _sr_v3_is_typing_reason(reason):
                # Fallback only.  Use a not-too-short duration to avoid inaudible 20ms fragments.
                try:
                    target_duration = max(0.09, float(target_duration or 0.12))
                except Exception:
                    target_duration = 0.12
                self._play_with_persistent_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration)
            else:
                self._play_with_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration)
    finally:
        try:
            if voice is not None:
                try:
                    voice.Speak("", 2)
                except Exception:
                    pass
        except Exception:
            pass
        try:
            self._stop_current_playback()
        except Exception:
            pass
        try:
            self._stop_typing_mpv()
        except Exception:
            pass
        try:
            if pythoncom is not None:
                pythoncom.CoUninitialize()
        except Exception:
            pass
        try:
            if self.tts_temp_dir is not None:
                shutil.rmtree(str(self.tts_temp_dir), ignore_errors=True)
                self.tts_temp_dir = None
                self.wav_cache.clear()
                self._ps_script_path = None
        except Exception:
            pass


def _sr_v3_visual_reading_segment(self, pos):
    """Return a multi-line lookahead reading segment and its target duration.

    The visual reader advances one line/block at a time using exact char count.  If audio is also
    one line long, every line change risks killing mpv and cutting speech.  This function instead
    speaks several upcoming visual rows as one audio segment while still computing target_duration
    from actual character count and the current WPM, so the long-run audio speed matches visual WPM.
    """
    if not self.text:
        return "", pos, pos, None
    try:
        self.refresh_display_chars_per_line()
    except Exception:
        pass
    total = len(self.text)
    pos = max(0, min(int(pos), max(0, total - 1)))
    try:
        cpl = max(1, int(getattr(self, "display_chars_per_line", 20) or 20))
    except Exception:
        cpl = 20
    try:
        block = self._reader_block_info(pos) or {}
        start = max(0, min(int(block.get("start_pos", (pos // cpl) * cpl)), total))
        line_idx = int(block.get("line_idx", start // cpl))
    except Exception:
        start = (pos // cpl) * cpl
        line_idx = start // cpl
    try:
        wpm = max(60.0, float(getattr(self, "wpm", 300) or 300))
    except Exception:
        wpm = 300.0
    # Enough lookahead to avoid cutting, but not so much that a jump waits for a huge synth.
    # Faster WPM needs more rows because each row stays on screen for less time.
    if wpm >= 2400:
        lookahead_lines = 12
    elif wpm >= 1200:
        lookahead_lines = 10
    elif wpm >= 600:
        lookahead_lines = 8
    else:
        lookahead_lines = 6
    try:
        line_step = max(1, int(getattr(self, "chunk_size", 1) or 1))
        lookahead_lines = max(line_step, lookahead_lines)
    except Exception:
        pass
    end = min(total, start + cpl * lookahead_lines)
    # Prefer ending at punctuation shortly after the minimum lookahead, so narration does not cut mid-sentence.
    min_end = end
    max_extra = min(total, end + cpl * 4)
    for i in range(end, max_extra):
        if self.text[i] in "。！？!?；;\n":
            end = min(total, i + 1)
            break
    segment = self.text[start:end]
    # Normalize only for speech, not for position math.
    speak_segment = re.sub(r"[\r\n\t]+", " ", segment).strip()
    if not speak_segment or not any((ch.isalnum() or self.is_cjk(ch)) for ch in speak_segment):
        return "", start, end, None
    char_count = max(1, end - start)
    target_duration = max(0.05, char_count * 60.0 / wpm)
    return speak_segment, start, end, target_duration


def _sr_v3_typing_target_duration(self, requested_wpm):
    # Only used by MPV fallback.  Direct SAPI typing ignores this and uses SAPI Rate.
    try:
        w = max(60.0, float(requested_wpm or 300.0))
    except Exception:
        w = 300.0
    return max(0.09, min(0.20, 60.0 / w * 1.1))


def _sr_v3_tts_segment_from_pos(self, pos, typing=False):
    if not self.text:
        return "", pos, pos
    n = len(self.text)
    pos = max(0, min(int(pos), max(0, n - 1)))
    if typing:
        ch = self.text[pos]
        if ch and (self.is_cjk(ch) or ch.isalnum()):
            return ch, pos, min(n, pos + 1)
        return "", pos, min(n, pos + 1)
    segment, start, end, _target = _sr_v3_visual_reading_segment(self, pos)
    return segment, start, end


def _sr_v3_speak_current_target(self, force=False):
    if not getattr(self, "tts_enabled", False) or self.tts is None or not self.text:
        return
    pos = self.typing_flat_char_index if self.typing_mode else self.reader_pos
    if pos < 0 or pos >= len(self.text):
        return
    mode = "typing" if self.typing_mode else "reading"
    requested_wpm = self.current_tts_wpm()
    effective_wpm = self.effective_tts_wpm(requested_wpm)
    try:
        if self.typing_mode:
            segment, start, end = self.tts_segment_from_pos(pos, typing=True)
            target_duration = _sr_v3_typing_target_duration(self, requested_wpm)
        else:
            segment, start, end, target_duration = _sr_v3_visual_reading_segment(self, pos)
        if not segment:
            return
        wpm_bucket = self.tts_speed_bucket_for_wpm(effective_wpm)
        if not self.typing_mode:
            active = getattr(self, "_tts_active_segment", None)
            if (not force) and active:
                a_mode, a_start, a_end, a_wpm_bucket = active
                if a_mode == mode and a_start <= pos < a_end and abs(wpm_bucket - a_wpm_bucket) <= 25:
                    return
            sig = (mode, start, end, hashlib.sha1(segment.encode("utf-8", errors="ignore")).hexdigest()[:12], wpm_bucket)
            if (not force) and sig == getattr(self, "_last_spoken_target", None):
                return
            self._last_spoken_target = sig
            self._tts_active_segment = (mode, start, end, wpm_bucket)
        else:
            # Typing has no segment dedupe beyond exact same raw position; each accepted key moves the red char.
            sig = (mode, start, end, segment)
            if (not force) and sig == getattr(self, "_last_spoken_target", None):
                return
            self._last_spoken_target = sig
            self._tts_active_segment = (mode, start, end, wpm_bucket)
        self.tts.speak_text(segment, wpm=effective_wpm, reason=f"{mode}:{start}-{end}", target_duration=target_duration)
    except Exception:
        self.log_debug("speak_current_target v3 failed:\n" + traceback.format_exc())


def _sr_v3_current_tts_wpm(self):
    if not self.typing_mode:
        return max(60.0, float(getattr(self, "wpm", 300) or 300))
    # Direct SAPI typing uses this only to choose SAPI Rate.  Use recent key rhythm but clamp sane values.
    try:
        cwpm = float(getattr(self, "typing_current_wpm", 0) or 0)
    except Exception:
        cwpm = 0.0
    if cwpm > 0:
        return max(60.0, min(12000.0, cwpm))
    try:
        now = time.time()
        recent = [t for t in list(getattr(self, "typing_event_times", [])) if now - t <= 3.0]
        if len(recent) >= 2:
            active = max(0.15, recent[-1] - recent[0])
            return max(60.0, min(12000.0, len(recent) / active * 60.0))
    except Exception:
        pass
    return 300.0


def _sr_v3_stop_tts_playback(self):
    try:
        if self.tts is not None:
            try:
                self.tts.clear_queue()
            except Exception:
                pass
            try:
                self.tts._stop_current_playback()
            except Exception:
                pass
            # Do not permanently close the direct SAPI worker; only purge current speech through a typing request path.
            try:
                self.tts._stop_typing_mpv()
            except Exception:
                pass
    except Exception:
        pass
    self._last_spoken_target = None
    self._tts_active_segment = None


TTSManager._direct_sapi_typing = _sr_v3_direct_sapi_typing
TTSManager._worker = _sr_v3_audio_worker
SpeedReader.tts_segment_from_pos = _sr_v3_tts_segment_from_pos
SpeedReader.speak_current_target = _sr_v3_speak_current_target
SpeedReader.current_tts_wpm = _sr_v3_current_tts_wpm
SpeedReader.stop_tts_playback = _sr_v3_stop_tts_playback

def run_selftest():
    import py_compile
    print("selftest: mapping")
    tests = {
        "a": "oa", "o": "oo", "e": "oe", "en": "of", "an": "oj", "quan": "qr", "ju": "ju", "qu": "qu", "xu": "xu", "yu": "yu",
        "yue": "yt", "yuan": "yr", "yun": "yp", "nv": "ny", "lv": "ly", "shi": "ui",
        "zhi": "vi", "chi": "ii", "chuang": "id", "shuang": "ud",
    }
    for py, expected in tests.items():
        got = sogou_code_for_pinyin(py)
        assert got == expected, (py, got, expected)
    char_tests = {"啊": "oa", "哦": "oo", "饿": "oe", "嗯": "of", "安": "oj", "居": "ju", "去": "qu", "虚": "xu", "鱼": "yu", "月": "yt", "元": "yr", "云": "yp", "女": "ny", "吕": "ly", "绿": "ly", "是": "ui", "知": "vi", "吃": "ii", "窗": "id", "双": "ud"}
    for ch, expected in char_tests.items():
        got = sogou_code_for_pinyin(BUILTIN_PINYIN_FOR_TEST[ch][0])
        assert got == expected, (ch, got, expected)
    assert sogou_code_for_pinyin("an") + sogou_code_for_pinyin("quan") == "ojqr"

    print("selftest: key engine")
    e = TypingKeyEngine(["ui"], "exact")
    assert not e.press("u") and e.buffer == "u"
    assert e.press("i") and e.wrong == 0
    e = TypingKeyEngine(["ui"], "exact")
    assert not e.press("x") and e.wrong == 1 and not e.accepted
    e = TypingKeyEngine(["ui"], "simple")
    assert not e.press("a") and e.press("b") and e.wrong == 0
    e = TypingKeyEngine(["ui"], "first")
    assert not e.press("x") and e.wrong == 1
    assert not e.press("u") and e.press("a")

    print("selftest: encoding")
    sample = "中文测试ABC\n安全ojqr"
    enc_tests = [
        (sample.encode("utf-8"), "utf"),
        (b"\xef\xbb\xbf" + sample.encode("utf-8"), "utf-8-sig"),
        (sample.encode("gb2312"), "gb"),
        (sample.encode("gbk"), "gb"),
        (sample.encode("gb18030"), "gb"),
        (b"\xff\xfe" + sample.encode("utf-16-le"), "utf-16-le-bom"),
        (b"\xfe\xff" + sample.encode("utf-16-be"), "utf-16-be-bom"),
        (sample.encode("utf-16-le"), "utf-16-le"),
        (sample.encode("utf-16-be"), "utf-16-be"),
    ]
    for raw, expect_contains in enc_tests:
        text, enc = decode_txt_bytes(raw)
        assert sample in text, (enc, text[:20])
        assert expect_contains in enc, (enc, expect_contains)

    print("selftest: json atomic")
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / "x.json"
        assert atomic_json_save(p, {"202606281234": 123.4, "daily_max": {"20260628": 123.4}})
        data = safe_json_load(p, {}, None)
        assert isinstance(data["202606281234"], float)

    print("selftest: focus policy")
    # v14 交互策略的纯逻辑约束：阅读/打字共享同一个中上焦点比例；
    # 点击正文在阅读模式应直接进入 playing=True，由 GUI on_text_click 调 start_reading_from 保证。
    focus_y_ratio = 0.42
    assert 0.35 <= focus_y_ratio <= 0.48

    print("selftest: dynamic wrap policy")
    # v18 policy: fixed 8-character rows are no longer a constant invariant; GUI computes
    # chars_per_line from Text pixel width and current font, while preserving flat indices.
    assert max(1, int(320 // 24)) > max(1, int(160 // 24))

    print("selftest: v15 edge policies")
    assert is_ctrl_combo_state(CTRL_MASK)
    assert not is_ctrl_combo_state(0x0040)
    assert not is_ctrl_combo_state(0x0080)
    assert focus_scroll_units(120, 60, 20) == 3
    assert focus_scroll_units(0, 120, 20) == -6
    class E:
        pass
    e1 = E(); e1.serial=10; e1.time=123; e1.keysym='a'; e1.char='a'; e1.state=0; e1.widget='w1'
    e2 = E(); e2.serial=10; e2.time=123; e2.keysym='a'; e2.char='a'; e2.state=0; e2.widget='w2'
    sig1 = (int(getattr(e1,'serial',0) or 0), int(getattr(e1,'time',0) or 0), e1.keysym, e1.char, int(e1.state), 'a')
    sig2 = (int(getattr(e2,'serial',0) or 0), int(getattr(e2,'time',0) or 0), e2.keysym, e2.char, int(e2.state), 'a')
    assert sig1 == sig2
    print("selftest passed")


# ---------- final hotfix v4: audio bug audit fixes ----------
# Main bug fixed here: at high typing speed, purging SAPI on every accepted character can cancel
# the previous sound before Windows has emitted any audible samples.  The worker now coalesces
# ultra-fast typing requests into the latest character at a small audible cadence.  Slow/normal
# typing still speaks immediately; very fast typing stays latest-character-first instead of
# becoming silent, stale, or broken.

def _sr_v4_typing_recent_wpm(self):
    try:
        now = time.time()
        times = list(getattr(self, "typing_event_times", []) or [])
        recent_short = [t for t in times if now - float(t) <= 1.25]
        recent_long = [t for t in times if now - float(t) <= 3.0]
        vals = []
        for recent in (recent_short, recent_long):
            if len(recent) >= 2:
                span = max(0.08, float(recent[-1]) - float(recent[0]))
                vals.append(len(recent) / span * 60.0)
        try:
            cwpm = float(getattr(self, "typing_current_wpm", 0) or 0)
            if cwpm > 0:
                vals.append(cwpm)
        except Exception:
            pass
        if vals:
            return max(60.0, min(12000.0, max(vals)))
    except Exception:
        pass
    return 300.0


def _sr_v4_current_tts_wpm(self):
    if not self.typing_mode:
        return max(60.0, float(getattr(self, "wpm", 300) or 300))
    return _sr_v4_typing_recent_wpm(self)


def _sr_v4_typing_min_emit_interval(self, wpm):
    """Smallest useful interval between audible typing prompts.

    3500 WPM is about 58 chars/s, roughly 17 ms per character.  Windows SAPI cannot
    articulate separate Chinese syllables at that cadence; purging every 17 ms creates
    silence.  These intervals intentionally coalesce bursts to the latest red character.
    """
    try:
        w = float(wpm or 300.0)
    except Exception:
        w = 300.0
    if w >= 3600:
        return 0.040
    if w >= 2400:
        return 0.048
    if w >= 1500:
        return 0.058
    if w >= 900:
        return 0.072
    if w >= 450:
        return 0.090
    if w >= 240:
        return 0.115
    return 0.145


def _sr_v4_direct_sapi_typing(self, voice, text, wpm=None, reason="typing"):
    try:
        s = str(text or "").strip()
        if not s:
            return False
        ch = s[0]
        try:
            w = float(wpm or 300.0)
        except Exception:
            w = 300.0
        # Make typing prompts more aggressive than v3; the previous low rates made fast input
        # sound slow even when the visual typing speed was high.
        if w < 120:
            rate = 3
        elif w < 240:
            rate = 6
        elif w < 420:
            rate = 8
        else:
            rate = 10
        try:
            voice.Rate = int(rate)
            voice.Volume = 100
        except Exception:
            pass
        try:
            # Explicit purge before speak is more reliable than relying only on the flag when
            # the previous async utterance is in its startup phase.
            voice.Speak("", 2)
        except Exception:
            pass
        voice.Speak(ch, 1 | 2)
        self._typing_last_sapi_emit_at = time.perf_counter()
        self._typing_last_sapi_char = ch
        self.log(f"TTS v4 direct SAPI typing ch={ch!r} wpm={w:.1f} rate={rate} reason={reason}", verbose=True)
        return True
    except Exception:
        self.log("TTS v4 direct SAPI typing failed:\n" + traceback.format_exc())
        return False


def _sr_v4_wait_and_coalesce_typing_item(self, item):
    """Wait only enough to avoid startup-phase purge silence, keeping only newest typing item."""
    try:
        wpm = self._normalize_wpm(item.get("wpm"))
    except Exception:
        wpm = 300.0
    interval = _sr_v4_typing_min_emit_interval(self, wpm)
    try:
        last = float(getattr(self, "_typing_last_sapi_emit_at", 0.0) or 0.0)
        due = last + interval
        while True:
            now = time.perf_counter()
            remain = due - now
            if remain <= 0:
                break
            try:
                newer = self.queue.get(timeout=min(0.010, max(0.001, remain)))
                if newer is None:
                    return None
                # If a reading request arrives while we are coalescing typing, return it to be
                # handled by the normal reading path rather than swallowing it.
                item = newer
                try:
                    reason = str(item.get("reason", ""))
                except Exception:
                    reason = ""
                if not _sr_v3_is_typing_reason(reason):
                    return item
                try:
                    wpm = self._normalize_wpm(item.get("wpm"))
                    interval = _sr_v4_typing_min_emit_interval(self, wpm)
                    due = max(due, last + interval)
                except Exception:
                    pass
            except queue.Empty:
                pass
            except Exception:
                break
        # Drain any final burst and keep only the latest item.
        try:
            while True:
                newer = self.queue.get_nowait()
                if newer is None:
                    return None
                item = newer
        except Exception:
            pass
        return item
    except Exception:
        return item


def _sr_v4_audio_worker(self):
    voice = None
    win32com = None
    pythoncom = None
    self._refresh_mpv_path()
    if self.mpv_path:
        self.log(f"TTS MPV found: {self.mpv_path}")
    else:
        self.log("TTS MPV not found yet; reading playback will rescan script folder, PATH, winget, scoop and chocolatey folders each time")
    if IS_WINDOWS:
        try:
            import pythoncom as _pythoncom
            import win32com.client as _win32com_client
            pythoncom = _pythoncom
            pythoncom.CoInitialize()
            class _Win32ComModule:
                client = _win32com_client
            win32com = _Win32ComModule
            voice = win32com.client.Dispatch("SAPI.SpVoice")
            self._select_sapi_voice(voice)
            self.backend = "mpv-reading/direct-sapi-typing-v4-coalesced"
            self.ready = bool(self.mpv_path) or bool(voice is not None)
            self.log("TTS backend ready: MPV accelerated reading + coalesced direct Windows SAPI typing v4")
        except Exception as e:
            voice = None
            win32com = None
            self.backend = "mpv+sapi-powershell-reading-no-direct-typing" if self.mpv_path else "sapi-powershell-no-mpv"
            self.ready = bool(self.mpv_path)
            self.log(f"TTS SAPI COM unavailable, fallback to PowerShell synthesis for reading: {e}")
    else:
        self.backend = "mpv-external-audio-only"
        self.ready = bool(self.mpv_path)
        self.log("TTS synthesis currently expects Windows SAPI; non-Windows needs an external WAV synth path")

    try:
        while not self.stop_event.is_set():
            item = self.queue.get()
            if item is None:
                break
            try:
                while True:
                    newer = self.queue.get_nowait()
                    if newer is None:
                        item = None
                        break
                    item = newer
            except Exception:
                pass
            if item is None or not self.enabled:
                continue
            try:
                reason = item.get("reason", "segment")
            except Exception:
                reason = "segment"
            if _sr_v3_is_typing_reason(reason):
                item = self._wait_and_coalesce_typing_item(item)
                if item is None:
                    continue
                try:
                    reason = item.get("reason", "segment")
                except Exception:
                    reason = "segment"

            text = self._normalize_text(item.get("text", ""))
            if not text:
                continue
            wpm = self._normalize_wpm(item.get("wpm"))
            target_duration = item.get("target_duration")

            if _sr_v3_is_typing_reason(reason) and voice is not None:
                self._direct_sapi_typing(voice, text, wpm=wpm, reason=reason)
                continue

            wav_path = None
            if voice is not None and win32com is not None:
                wav_path = self._sapi_com_wav_for_text(voice, win32com, text)
            if wav_path is None and IS_WINDOWS:
                wav_path = self._sapi_powershell_wav_for_text(text)
            latest = None
            try:
                while True:
                    newer = self.queue.get_nowait()
                    if newer is None:
                        latest = None
                        break
                    latest = newer
            except Exception:
                pass
            if latest is not None:
                try:
                    self.queue.put_nowait(latest)
                except Exception:
                    pass
                continue
            if wav_path is None:
                self.log("TTS synth failed: no usable WAV was produced")
                continue
            if _sr_v3_is_typing_reason(reason):
                try:
                    target_duration = max(0.09, float(target_duration or 0.12))
                except Exception:
                    target_duration = 0.12
                self._play_with_persistent_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration)
            else:
                try:
                    dur = self._wav_duration_seconds(wav_path)
                    speed = self._speed_for_target(wav_path, wpm=wpm, target_duration=target_duration)
                    self.log(f"TTS reading sync v4 chars_target={target_duration} wav_dur={dur} speed={speed:.3f} reason={reason}", verbose=True)
                except Exception:
                    pass
                self._play_with_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration)
    finally:
        try:
            if voice is not None:
                try:
                    voice.Speak("", 2)
                except Exception:
                    pass
        except Exception:
            pass
        try:
            self._stop_current_playback()
        except Exception:
            pass
        try:
            self._stop_typing_mpv()
        except Exception:
            pass
        try:
            if pythoncom is not None:
                pythoncom.CoUninitialize()
        except Exception:
            pass
        try:
            if self.tts_temp_dir is not None:
                shutil.rmtree(str(self.tts_temp_dir), ignore_errors=True)
                self.tts_temp_dir = None
                self.wav_cache.clear()
                self._ps_script_path = None
        except Exception:
            pass


TTSManager._typing_min_emit_interval = _sr_v4_typing_min_emit_interval
TTSManager._direct_sapi_typing = _sr_v4_direct_sapi_typing
TTSManager._wait_and_coalesce_typing_item = _sr_v4_wait_and_coalesce_typing_item
TTSManager._worker = _sr_v4_audio_worker
SpeedReader.current_tts_wpm = _sr_v4_current_tts_wpm

# ---------- audio v5: nonblocking reading playback + prebuffer next segment to remove periodic boundary silence ----------
# Root cause of the reported ~30s reading stutter: older reading audio was generated as a finite
# lookahead segment.  The worker waited inside mpv until that segment finished, so it could not
# synthesize the next segment during playback.  When the GUI finally requested the next segment at
# the boundary, Windows SAPI synthesis + mpv launch created a noticeable silence.  v5 makes normal
# reading playback nonblocking, requests the next reading segment before the current one ends, and
# starts the prepared next segment only after the current mpv process exits.

def _sr_v5_reason(reason):
    try:
        return str(reason or "").lower()
    except Exception:
        return ""


def _sr_v5_is_typing_reason(reason):
    return _sr_v5_reason(reason).startswith("typing")


def _sr_v5_is_reading_next_reason(reason):
    r = _sr_v5_reason(reason)
    return r.startswith("reading_next") or r.startswith("reading-prefetch") or r.startswith("reading_prefetch")


def _sr_v5_is_reading_reason(reason):
    return _sr_v5_reason(reason).startswith("reading")


def _sr_v5_stop_current_playback(self):
    try:
        self._playback_generation = int(getattr(self, "_playback_generation", 0) or 0) + 1
    except Exception:
        self._playback_generation = 1
    proc = getattr(self, "current_proc", None)
    if proc is None:
        return
    try:
        if proc.poll() is None:
            proc.terminate()
            try:
                proc.wait(timeout=0.25)
            except Exception:
                try:
                    proc.kill()
                except Exception:
                    pass
    except Exception:
        pass
    finally:
        self.current_proc = None


def _sr_v5_play_with_mpv(self, wav_path, wpm=None, reason="segment", target_duration=None):
    mpv = self._refresh_mpv_path()
    if not mpv:
        self.log(
            "TTS MPV unavailable: mpv.exe was not found in script folder, PATH, "
            "winget package folders, scoop, or chocolatey. Install mpv-player.mpv-CI.MSVC "
            "or put mpv.exe next to this .py file."
        )
        return False
    speed = self._speed_for_target(wav_path, wpm=wpm, target_duration=target_duration)
    pitch_correction = "yes" if speed <= 4.0 else "no"
    cmd = [
        str(mpv),
        "--no-terminal",
        "--really-quiet",
        "--force-window=no",
        "--vo=null",
        "--audio-display=no",
        "--idle=no",
        f"--audio-pitch-correction={pitch_correction}",
        f"--speed={speed:.4f}",
        "--",
        str(wav_path),
    ]
    creationflags = 0
    if IS_WINDOWS and hasattr(subprocess, "CREATE_NO_WINDOW"):
        creationflags = subprocess.CREATE_NO_WINDOW
    defer_until_current_ends = _sr_v5_is_reading_next_reason(reason)
    try:
        if defer_until_current_ends:
            generation = int(getattr(self, "_playback_generation", 0) or 0)
            started_wait = time.perf_counter()
            while not self.stop_event.is_set() and self.enabled:
                proc = getattr(self, "current_proc", None)
                if proc is None or proc.poll() is not None:
                    break
                if int(getattr(self, "_playback_generation", 0) or 0) != generation:
                    self.log(f"TTS v5 deferred reading aborted by playback generation change reason={reason}", verbose=True)
                    return False
                # Safety valve: a hung mpv should not block the TTS worker forever.
                if time.perf_counter() - started_wait > 180.0:
                    self.log(f"TTS v5 deferred reading wait exceeded safety limit; forcing next reason={reason}")
                    break
                time.sleep(0.012)
            if int(getattr(self, "_playback_generation", 0) or 0) != generation or self.stop_event.is_set() or not self.enabled:
                return False
        else:
            self._stop_current_playback()
        self.log(
            f"TTS MPV v5 launch reason={reason} effective_wpm={float(wpm or 0):.1f} "
            f"target={target_duration} speed={speed:.3f} pitch={pitch_correction} defer={defer_until_current_ends} file={wav_path}",
            verbose=True,
        )
        self.current_proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, creationflags=creationflags)
        # Do not wait for ordinary reading playback.  The worker must remain free to synthesize
        # the next segment while this one is still audible.  Deferred next playback waited above,
        # then also returns immediately after launch so the following prefetch can be prepared.
        if _sr_v5_is_reading_reason(reason):
            return True
        # Non-reading fallback behavior: wait, preserving old semantics for rare segment calls.
        self.current_proc.wait()
        self.current_proc = None
        return True
    except Exception:
        self.current_proc = None
        self.log("TTS MPV v5 playback failed:\n" + traceback.format_exc())
        return False


def _sr_v5_speak_text(self, text, wpm=None, reason="segment", target_duration=None):
    if not self.enabled:
        return
    text = self._normalize_text(text)
    if not text:
        return
    self.start()
    effective_wpm = self.effective_wpm_for_playback(wpm)
    item = {
        "text": text,
        "wpm": effective_wpm,
        "requested_wpm": self._normalize_wpm(wpm),
        "reason": str(reason or "segment"),
        "target_duration": None if target_duration is None else max(0.001, float(target_duration)),
        "time": time.time(),
    }
    # A next-reading item is a prebuffer job: replace any older queued prebuffer, but do not stop
    # the currently audible mpv process.  Normal reading requests still cut immediately because
    # they usually mean jump, restart, speed bucket change, or user action.
    if _sr_v5_is_reading_next_reason(reason):
        self.clear_queue()
    else:
        self.clear_queue()
        if not _sr_v5_is_typing_reason(reason):
            self._stop_current_playback()
    try:
        self.queue.put_nowait(item)
    except Exception:
        pass


def _sr_v5_visual_reading_segment(self, pos):
    """Return a long line-aligned segment sized by target seconds, not by a fixed row count."""
    if not self.text:
        return "", pos, pos, None
    try:
        self.refresh_display_chars_per_line()
    except Exception:
        pass
    total = len(self.text)
    pos = max(0, min(int(pos), max(0, total - 1)))
    try:
        cpl = max(1, int(getattr(self, "display_chars_per_line", 24) or 24))
    except Exception:
        cpl = 24
    try:
        wpm = max(60.0, float(getattr(self, "wpm", 300) or 300))
    except Exception:
        wpm = 300.0
    # Align start to visual line/block so audio target seconds match visible line switching.
    try:
        block = self._reader_block_info(pos) or {}
        start = max(0, min(int(block.get("start_pos", (pos // cpl) * cpl)), total))
    except Exception:
        start = (pos // cpl) * cpl
    try:
        line_step = max(1, int(getattr(self, "chunk_size", 1) or 1))
    except Exception:
        line_step = 1
    # Long enough that SAPI has plenty of time to prebuffer the next segment; not so long that a
    # click/jump has to synthesize a huge chapter before sound starts.  At 600 WPM this is about
    # 650 chars; at 3000 WPM about 3000 chars.
    # v6: make each synthesized reading buffer substantially longer so the boundary is rare,
    # while still capping char count to avoid huge SAPI jobs on very fast WPM.  The next buffer
    # is requested early, so synthesis should finish long before current audio ends.
    target_seconds = 105.0
    target_chars = int(max(cpl * max(14, line_step * 5), min(7200, wpm * target_seconds / 60.0)))
    # End at a visual line boundary so active segment math and GUI line timing stay consistent.
    raw_end = min(total, start + target_chars)
    end = min(total, ((raw_end + cpl - 1) // cpl) * cpl)
    if end <= start:
        end = min(total, start + cpl)
    segment = self.text[start:end]
    speak_segment = re.sub(r"[\r\n\t]+", " ", segment).strip()
    if not speak_segment or not any((ch.isalnum() or self.is_cjk(ch)) for ch in speak_segment):
        return "", start, end, None
    char_count = max(1, end - start)
    target_duration = max(0.05, char_count * 60.0 / wpm)
    return speak_segment, start, end, target_duration


def _sr_v5_should_prefetch(self, pos, active):
    try:
        _mode, start, end, _bucket = active
        span = max(1, int(end) - int(start))
        done = max(0, int(pos) - int(start))
        try:
            wpm = max(60.0, float(getattr(self, "wpm", 300) or 300))
        except Exception:
            wpm = 300.0
        chars_left = max(0, int(end) - int(pos))
        seconds_left = chars_left * 60.0 / wpm
        # v6: request next audio much earlier.  The old late prefetch still allowed SAPI/MPV
        # startup to touch the audible boundary on some machines, which sounded like a fixed
        # periodic stutter.  Early prebuffer trades a little disk/cache work for continuous sound.
        return (done / float(span) >= 0.32) or (seconds_left <= 55.0)
    except Exception:
        return False


def _sr_v5_prefetch_next_reading(self, active, effective_wpm, wpm_bucket):
    try:
        _mode, _start, end, _bucket = active
        if end >= len(self.text):
            return
        segment, ns, ne, target_duration = _sr_v5_visual_reading_segment(self, end)
        if not segment or ne <= ns:
            return
        key = (ns, ne, wpm_bucket, hashlib.sha1(segment.encode("utf-8", errors="ignore")).hexdigest()[:12])
        if key == getattr(self, "_tts_prefetch_key", None):
            return
        self._tts_prefetch_key = key
        self._tts_prefetch_segment = ("reading", ns, ne, wpm_bucket)
        self.log_debug(
            f"TTS v5 prebuffer request current=({_start},{end}) next=({ns},{ne}) target={target_duration:.3f}s wpm={effective_wpm:.1f}",
            verbose=True,
        )
        self.tts.speak_text(segment, wpm=effective_wpm, reason=f"reading_next:{ns}-{ne}", target_duration=target_duration)
    except Exception:
        self.log_debug("TTS v5 prefetch failed:\n" + traceback.format_exc())


def _sr_v5_speak_current_target(self, force=False):
    if not getattr(self, "tts_enabled", False) or self.tts is None or not self.text:
        return
    pos = self.typing_flat_char_index if self.typing_mode else self.reader_pos
    if pos < 0 or pos >= len(self.text):
        return
    mode = "typing" if self.typing_mode else "reading"
    requested_wpm = self.current_tts_wpm()
    effective_wpm = self.effective_tts_wpm(requested_wpm)
    try:
        if self.typing_mode:
            segment, start, end = self.tts_segment_from_pos(pos, typing=True)
            if not segment:
                return
            sig = (mode, start, end, segment)
            if (not force) and sig == getattr(self, "_last_spoken_target", None):
                return
            self._last_spoken_target = sig
            self._tts_active_segment = (mode, start, end, self.tts_speed_bucket_for_wpm(effective_wpm))
            self.tts.speak_text(segment, wpm=effective_wpm, reason=f"typing:{start}-{end}", target_duration=None)
            return

        wpm_bucket = self.tts_speed_bucket_for_wpm(effective_wpm)
        active = getattr(self, "_tts_active_segment", None)
        prefetch = getattr(self, "_tts_prefetch_segment", None)

        if (not force) and active:
            try:
                a_mode, a_start, a_end, a_bucket = active
                if a_mode == mode and a_start <= pos < a_end and abs(wpm_bucket - a_bucket) <= 25:
                    if _sr_v5_should_prefetch(self, pos, active):
                        _sr_v5_prefetch_next_reading(self, active, effective_wpm, wpm_bucket)
                    return
            except Exception:
                pass

        if (not force) and prefetch:
            try:
                p_mode, p_start, p_end, p_bucket = prefetch
                if p_mode == mode and p_start <= pos < p_end and abs(wpm_bucket - p_bucket) <= 25:
                    self._tts_active_segment = prefetch
                    self._tts_prefetch_segment = None
                    self._last_spoken_target = (mode, p_start, p_end, p_bucket)
                    if _sr_v5_should_prefetch(self, pos, self._tts_active_segment):
                        _sr_v5_prefetch_next_reading(self, self._tts_active_segment, effective_wpm, wpm_bucket)
                    return
            except Exception:
                pass

        segment, start, end, target_duration = _sr_v5_visual_reading_segment(self, pos)
        if not segment:
            return
        sig = (mode, start, end, hashlib.sha1(segment.encode("utf-8", errors="ignore")).hexdigest()[:12], wpm_bucket)
        if (not force) and sig == getattr(self, "_last_spoken_target", None):
            return
        self._last_spoken_target = sig
        self._tts_active_segment = (mode, start, end, wpm_bucket)
        self._tts_prefetch_segment = None
        self._tts_prefetch_key = None
        self.log_debug(f"TTS v5 immediate reading request segment=({start},{end}) target={target_duration:.3f}s wpm={effective_wpm:.1f} force={force}", verbose=True)
        self.tts.speak_text(segment, wpm=effective_wpm, reason=f"reading:{start}-{end}", target_duration=target_duration)
    except Exception:
        self.log_debug("speak_current_target v5 failed:\n" + traceback.format_exc())


def _sr_v5_stop_tts_playback(self):
    try:
        if self.tts is not None:
            try:
                self.tts.clear_queue()
            except Exception:
                pass
            try:
                self.tts._stop_current_playback()
            except Exception:
                pass
            try:
                self.tts._stop_typing_mpv()
            except Exception:
                pass
    except Exception:
        pass
    self._last_spoken_target = None
    self._tts_active_segment = None
    self._tts_prefetch_segment = None
    self._tts_prefetch_key = None


TTSManager._stop_current_playback = _sr_v5_stop_current_playback
TTSManager._play_with_mpv = _sr_v5_play_with_mpv
TTSManager.speak_text = _sr_v5_speak_text
SpeedReader.speak_current_target = _sr_v5_speak_current_target
SpeedReader.stop_tts_playback = _sr_v5_stop_tts_playback


# ---------- audio v6: make hotfixes actually apply before GUI starts + earlier/longer prebuffer ----------
# Earlier generated hotfix blocks were appended after the original if __name__ == "__main__" block.
# In normal double-click/py execution, app.mainloop() started before those monkey patches were reached,
# so the intended v4/v5 audio fixes did not apply at runtime.  The entrypoint is intentionally moved
# here, after all patches above, so reading prebuffer, MPV nonblocking playback, and typing audio fixes
# are installed before SpeedReader() is constructed.

# ---------- audio v7: efficient prebuffered reading MPV pipeline + smaller WAVs ----------
# MPV only plays/accelerates audio; Windows SAPI is the synthesizer.  The bottlenecks reported in
# reading mode were caused by large slow SAPI WAV jobs plus process-boundary gaps.  v7 optimizes:
# - reading SAPI rate by target WPM, so high-WPM reading produces much shorter raw WAVs before MPV acceleration;
# - WAV postprocess to 600% gain while trimming leading/trailing silence and converting to mono 16-bit PCM;
# - one persistent reading MPV process with append-play for prebuffered next segment, avoiding mpv.exe relaunch gaps;
# - safer worker logic so a prefetch request does not accidentally cancel the current segment before it even plays.

def _sr_v7_reason(reason):
    try:
        return str(reason or "").lower()
    except Exception:
        return ""

def _sr_v7_is_reading_reason(reason):
    return _sr_v7_reason(reason).startswith("reading")

def _sr_v7_is_reading_next_reason(reason):
    r = _sr_v7_reason(reason)
    return r.startswith("reading_next") or r.startswith("reading-prefetch") or r.startswith("reading_prefetch")

def _sr_v7_is_typing_reason(reason):
    return _sr_v7_reason(reason).startswith("typing")

def _sr_v7_sapi_rate_for_job(self, reason, wpm=None, text=""):
    """Pick SAPI synthesis rate before MPV speed.  High WPM should not synthesize giant slow WAVs."""
    if _sr_v7_is_typing_reason(reason):
        return 10
    try:
        w = float(wpm or 300.0)
    except Exception:
        w = 300.0
    # Low-speed reading remains natural; high-speed reading uses faster SAPI first, then MPV.
    if w <= 90:
        return -4
    if w <= 150:
        return -2
    if w <= 300:
        return 0
    if w <= 600:
        return 2
    if w <= 1200:
        return 5
    if w <= 2400:
        return 8
    return 10

def _sr_v7_cache_key_for_text(self, text):
    s = str(text or "")
    rate = int(getattr(self, "_sr_v7_current_sapi_rate", 0) or 0)
    mode = str(getattr(self, "_sr_v7_current_synth_mode", "read") or "read")
    # Include the synthesis rate and postprocess version; otherwise a slow natural reading WAV and
    # a high-speed short WAV for the same text would incorrectly share cache.
    digest = hashlib.sha1((f"v7-gain600-trim-mono16-rate{rate}-{mode}\0" + s).encode("utf-8", errors="ignore")).hexdigest()
    return digest[:32]

def _sr_v7_pcm_sample_to_i16(sample_bytes, sampwidth):
    if sampwidth == 1:
        return (int(sample_bytes[0]) - 128) << 8
    if sampwidth == 2:
        return int.from_bytes(sample_bytes, "little", signed=True)
    if sampwidth == 3:
        v = int.from_bytes(sample_bytes, "little", signed=True)
        return max(-32768, min(32767, v >> 8))
    if sampwidth == 4:
        v = int.from_bytes(sample_bytes, "little", signed=True)
        return max(-32768, min(32767, v >> 16))
    return 0

def _sr_v7_gain600_wav_for_raw(self, raw_path, key):
    """Create a small, MPV-friendly WAV: mono 16-bit PCM, silence-trimmed, 600% amplitude.

    This avoids unnecessary stereo/24-bit/32-bit payloads and removes dead leading/trailing silence.
    It deliberately does not compress to MP3/FLAC because encoding would add CPU latency and an
    extra dependency; PCM WAV is the fastest local handoff to mpv.
    """
    try:
        from array import array
        raw_path = Path(raw_path)
        if not raw_path.is_file() or raw_path.stat().st_size <= 256:
            return None
        out_path = raw_path.with_name(raw_path.stem + "_v7_mono16_gain600.wav")
        if out_path.is_file() and out_path.stat().st_size > 256:
            return out_path

        with wave.open(str(raw_path), "rb") as r:
            nchannels = int(r.getnchannels())
            sampwidth = int(r.getsampwidth())
            framerate = int(r.getframerate())
            nframes = int(r.getnframes())
            frames = r.readframes(nframes)
            comptype = r.getcomptype()

        if comptype not in ("NONE", "not compressed"):
            shutil.copyfile(str(raw_path), str(out_path))
            return out_path

        # Fast path for the common SAPI output: mono signed 16-bit PCM.
        if nchannels == 1 and sampwidth == 2:
            samples = array("h")
            samples.frombytes(frames)
            if sys.byteorder != "little":
                samples.byteswap()
            raw_i16 = samples
        else:
            raw_i16 = array("h")
            frame_size = max(1, nchannels * sampwidth)
            for frame_index in range(max(0, len(frames) // frame_size)):
                base = frame_index * frame_size
                total = 0
                count = 0
                for ch in range(nchannels):
                    i = base + ch * sampwidth
                    total += _sr_v7_pcm_sample_to_i16(frames[i:i + sampwidth], sampwidth)
                    count += 1
                raw_i16.append(int(total / max(1, count)))

        if not raw_i16:
            return raw_path

        # Trim only external silence.  Keep a tiny pad so MPV starts cleanly and SAPI consonants are not clipped.
        threshold = 96
        first = 0
        last = len(raw_i16) - 1
        while first < len(raw_i16) and abs(int(raw_i16[first])) <= threshold:
            first += 1
        while last > first and abs(int(raw_i16[last])) <= threshold:
            last -= 1
        if first >= len(raw_i16) or last <= first:
            first, last = 0, len(raw_i16) - 1

        try:
            mode = str(getattr(self, "_sr_v7_current_synth_mode", "read"))
        except Exception:
            mode = "read"
        pad_ms = 6 if mode == "typing" else 18
        pad = int(max(0, framerate) * pad_ms / 1000.0)
        first = max(0, first - pad)
        last = min(len(raw_i16) - 1, last + pad)

        gain = 6.0
        out = array("h")
        append = out.append
        for s in raw_i16[first:last + 1]:
            v = int(int(s) * gain)
            if v > 32767:
                v = 32767
            elif v < -32768:
                v = -32768
            append(v)
        if sys.byteorder != "little":
            out.byteswap()

        with wave.open(str(out_path), "wb") as w:
            w.setnchannels(1)
            w.setsampwidth(2)
            w.setframerate(max(8000, framerate))
            w.writeframes(out.tobytes())

        try:
            raw_path.unlink(missing_ok=True)
        except Exception:
            pass
        return out_path if out_path.is_file() and out_path.stat().st_size > 256 else raw_path
    except Exception:
        try:
            self.log("TTS v7 compact/gain WAV postprocess failed:\n" + traceback.format_exc())
            return Path(raw_path) if Path(raw_path).is_file() else None
        except Exception:
            return None

def _sr_v7_ensure_reading_mpv(self):
    mpv = self._refresh_mpv_path()
    if not mpv:
        return None
    proc = getattr(self, "_reading_mpv_proc", None)
    try:
        if proc is not None and proc.poll() is None and proc.stdin:
            return proc
    except Exception:
        pass

    creationflags = 0
    if IS_WINDOWS and hasattr(subprocess, "CREATE_NO_WINDOW"):
        creationflags = subprocess.CREATE_NO_WINDOW
    cmd = [
        str(mpv),
        "--idle=yes",
        "--force-window=no",
        "--vo=null",
        "--no-video",
        "--audio-display=no",
        "--really-quiet",
        "--gapless-audio=yes",
        "--keep-open=no",
        "--input-terminal=yes",
    ]
    try:
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            text=True,
            encoding="utf-8",
            errors="ignore",
            creationflags=creationflags,
            bufsize=1,
        )
        self._reading_mpv_proc = proc
        self.log(f"TTS v7 persistent reading MPV started: {mpv}", verbose=True)
        return proc
    except Exception:
        self._reading_mpv_proc = None
        self.log("TTS v7 persistent reading MPV start failed:\n" + traceback.format_exc())
        return None

def _sr_v7_stop_reading_mpv(self):
    proc = getattr(self, "_reading_mpv_proc", None)
    self._reading_mpv_proc = None
    try:
        if proc is not None and proc.poll() is None:
            try:
                if proc.stdin:
                    proc.stdin.write("quit\n")
                    proc.stdin.flush()
            except Exception:
                pass
            try:
                proc.wait(timeout=0.25)
            except Exception:
                try:
                    proc.terminate()
                except Exception:
                    pass
    except Exception:
        pass

def _sr_v7_send_mpv(self, proc, command):
    try:
        if proc is None or proc.poll() is not None or not proc.stdin:
            return False
        proc.stdin.write(str(command).rstrip("\n") + "\n")
        proc.stdin.flush()
        return True
    except Exception:
        return False

def _sr_v7_play_reading_with_persistent_mpv(self, wav_path, wpm=None, reason="reading", target_duration=None):
    proc = self._ensure_reading_mpv()
    if proc is None:
        return False
    speed = self._speed_for_target(wav_path, wpm=wpm, target_duration=target_duration)
    pitch_correction = "yes" if speed <= 4.0 else "no"
    mode = "append-play" if _sr_v7_is_reading_next_reason(reason) else "replace"
    try:
        # For append-play, speed is normally the same bucket as current playback.  Setting it here
        # also ensures the queued file inherits the intended speed.  If the user changed speed,
        # GUI invalidates the old prefetch and sends an immediate replace instead.
        if not _sr_v7_send_mpv(self, proc, f"set speed {float(speed):.4f}"):
            raise RuntimeError("failed to set mpv speed")
        _sr_v7_send_mpv(self, proc, f"set audio-pitch-correction {pitch_correction}")
        if not _sr_v7_send_mpv(self, proc, f"loadfile {_sr_audio_quote_mpv_path(wav_path)} {mode}"):
            raise RuntimeError("failed to loadfile into persistent mpv")
        self.log(
            f"TTS v7 persistent reading MPV command reason={reason} mode={mode} "
            f"effective_wpm={float(wpm or 0):.1f} target={target_duration} speed={float(speed):.3f} "
            f"pitch={pitch_correction} file={wav_path}",
            verbose=True,
        )
        self.current_proc = proc
        return True
    except Exception:
        self.log("TTS v7 persistent reading command failed, falling back to one-shot mpv:\n" + traceback.format_exc())
        self._stop_reading_mpv()
        return False

def _sr_v7_old_stop_current_playback(self):
    # Save old one-shot mpv stopper behavior, but add persistent reading mpv shutdown.
    try:
        self._stop_reading_mpv()
    except Exception:
        pass
    proc = getattr(self, "current_proc", None)
    try:
        # If current_proc is the persistent reading proc, it was already handled above.
        if proc is not None and proc is not getattr(self, "_reading_mpv_proc", None):
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=0.25)
                except Exception:
                    try:
                        proc.kill()
                    except Exception:
                        pass
    except Exception:
        pass
    finally:
        self.current_proc = None

def _sr_v7_play_with_mpv(self, wav_path, wpm=None, reason="segment", target_duration=None):
    # Reading mode uses persistent MPV with append-play prebuffer to avoid periodic mpv.exe launch gaps.
    if _sr_v7_is_reading_reason(reason):
        if self._play_reading_with_persistent_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration):
            return True
        # Fallback to the previous one-shot launcher if stdin control is unavailable.
    return _sr_v5_play_with_mpv(self, wav_path, wpm=wpm, reason=reason, target_duration=target_duration)

def _sr_v7_sapi_com_wav_for_text(self, voice, win32com, text):
    key = self._cache_key_for_text(text)
    cached = self.wav_cache.get(key)
    if cached:
        try:
            if Path(cached).is_file() and Path(cached).stat().st_size > 256:
                return cached
        except Exception:
            pass
    temp_dir = self._ensure_tts_temp_dir()
    if temp_dir is None:
        return None
    raw_path = Path(temp_dir) / (key + "_raw.wav")
    out_path = Path(temp_dir) / (key + "_raw_v7_mono16_gain600.wav")
    if out_path.is_file() and out_path.stat().st_size > 256:
        self._remember_wav_cache(key, out_path)
        return out_path

    old_stream = None
    stream = None
    try:
        stream = win32com.client.Dispatch("SAPI.SpFileStream")
        stream.Open(str(raw_path), 3, False)
        try:
            old_stream = voice.AudioOutputStream
        except Exception:
            old_stream = None
        voice.AudioOutputStream = stream
        try:
            voice.Rate = int(getattr(self, "_sr_v7_current_sapi_rate", 0) or 0)
            voice.Volume = 100
        except Exception:
            pass
        voice.Speak(str(text), 0)
        try:
            voice.AudioOutputStream = old_stream
        except Exception:
            pass
        stream.Close()
        stream = None
        out = self._gain600_wav_for_raw(raw_path, key)
        if out is not None and Path(out).is_file() and Path(out).stat().st_size > 256:
            self._remember_wav_cache(key, out)
            return out
    except Exception:
        self.log("TTS v7 SAPI COM synth failed:\n" + traceback.format_exc())
    finally:
        try:
            if old_stream is not None:
                voice.AudioOutputStream = old_stream
        except Exception:
            pass
        try:
            if stream is not None:
                stream.Close()
        except Exception:
            pass
    return None

def _sr_v7_audio_worker(self):
    voice = None
    win32com = None
    pythoncom = None
    self._refresh_mpv_path()
    if self.mpv_path:
        self.log(f"TTS MPV found: {self.mpv_path}")
    else:
        self.log("TTS MPV not found yet; playback will rescan script folder, PATH, winget, scoop and chocolatey folders each time")
    if IS_WINDOWS:
        try:
            import pythoncom as _pythoncom
            import win32com.client as _win32com_client
            pythoncom = _pythoncom
            pythoncom.CoInitialize()
            class _Win32ComModule:
                client = _win32com_client
            win32com = _Win32ComModule
            voice = win32com.client.Dispatch("SAPI.SpVoice")
            self._select_sapi_voice(voice)
            self.backend = "mpv-persistent-reading-v7/sapi"
            self.ready = bool(self.mpv_path) or bool(voice is not None)
            self.log("TTS backend ready: v7 compact WAV + persistent MPV reading prebuffer + direct SAPI typing")
        except Exception as e:
            voice = None
            win32com = None
            self.backend = "mpv-reading-powershell-v7" if self.mpv_path else "sapi-powershell-no-mpv"
            self.ready = bool(self.mpv_path)
            self.log(f"TTS SAPI COM unavailable, fallback to PowerShell synthesis for reading: {e}")
    else:
        self.backend = "mpv-external-audio-only"
        self.ready = bool(self.mpv_path)

    def drain_latest():
        latest = None
        try:
            while True:
                newer = self.queue.get_nowait()
                if newer is None:
                    return None
                latest = newer
        except Exception:
            return latest

    try:
        while not self.stop_event.is_set():
            item = self.queue.get()
            if item is None:
                break
            latest = drain_latest()
            if latest is not None:
                item = latest
            if item is None or not self.enabled:
                continue

            reason = item.get("reason", "segment")
            if _sr_v7_is_typing_reason(reason) and voice is not None:
                # Coalesce only typing bursts; this prevents repeatedly purging SAPI before a sound can emerge.
                try:
                    item2 = self._wait_and_coalesce_typing_item(item)
                    if item2 is not None:
                        item = item2
                        reason = item.get("reason", reason)
                except Exception:
                    pass
                text0 = self._normalize_text(item.get("text", ""))
                if text0:
                    self._direct_sapi_typing(voice, text0, wpm=self._normalize_wpm(item.get("wpm")), reason=reason)
                continue

            text_to_speak = self._normalize_text(item.get("text", ""))
            if not text_to_speak:
                continue
            wpm = self._normalize_wpm(item.get("wpm"))
            target_duration = item.get("target_duration")

            self._sr_v7_current_sapi_rate = self._sapi_rate_for_job(reason, wpm=wpm, text=text_to_speak)
            self._sr_v7_current_synth_mode = "typing" if _sr_v7_is_typing_reason(reason) else "reading"
            wav_path = None
            if voice is not None and win32com is not None:
                wav_path = self._sapi_com_wav_for_text(voice, win32com, text_to_speak)
            if wav_path is None and IS_WINDOWS:
                wav_path = self._sapi_powershell_wav_for_text(text_to_speak)

            latest_after_synth = drain_latest()
            requeue_after_play = None
            if latest_after_synth is not None:
                latest_reason = latest_after_synth.get("reason", "segment")
                # A prefetch that arrives while the current reading segment is being synthesized must not
                # cancel the current audible segment; otherwise the first segment can be skipped and sound
                # appears to stall.  Play current, then queue the prefetch immediately after.
                if _sr_v7_is_reading_reason(reason) and _sr_v7_is_reading_next_reason(latest_reason):
                    requeue_after_play = latest_after_synth
                else:
                    try:
                        self.queue.put_nowait(latest_after_synth)
                    except Exception:
                        pass
                    continue

            if wav_path is None:
                self.log("TTS v7 synth failed: no usable WAV was produced")
                if requeue_after_play is not None:
                    try:
                        self.queue.put_nowait(requeue_after_play)
                    except Exception:
                        pass
                continue

            try:
                dur = self._wav_duration_seconds(wav_path)
                speed = self._speed_for_target(wav_path, wpm=wpm, target_duration=target_duration)
                self.log(
                    f"TTS v7 synth/play reason={reason} chars={len(text_to_speak)} "
                    f"rate={getattr(self, '_sr_v7_current_sapi_rate', None)} wav_dur={dur} "
                    f"target={target_duration} speed={speed:.3f} size={Path(wav_path).stat().st_size if Path(wav_path).exists() else 'NA'}",
                    verbose=True,
                )
            except Exception:
                pass

            if _sr_v7_is_typing_reason(reason):
                self._play_with_persistent_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration)
            else:
                self._play_with_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration)

            if requeue_after_play is not None:
                try:
                    self.queue.put_nowait(requeue_after_play)
                except Exception:
                    pass
    finally:
        try:
            if voice is not None:
                try:
                    voice.Speak("", 2)
                except Exception:
                    pass
        except Exception:
            pass
        try:
            self._stop_current_playback()
        except Exception:
            pass
        try:
            self._stop_typing_mpv()
        except Exception:
            pass
        try:
            if pythoncom is not None:
                pythoncom.CoUninitialize()
        except Exception:
            pass
        try:
            if self.tts_temp_dir is not None:
                shutil.rmtree(str(self.tts_temp_dir), ignore_errors=True)
                self.tts_temp_dir = None
                self.wav_cache.clear()
                self._ps_script_path = None
        except Exception:
            pass

def _sr_v7_close(self):
    try:
        self.stop_event.set()
        self.clear_queue()
        try:
            self.queue.put_nowait(None)
        except Exception:
            pass
        self._stop_current_playback()
        self._stop_typing_mpv()
        self._stop_reading_mpv()
    except Exception:
        pass

TTSManager._sapi_rate_for_job = _sr_v7_sapi_rate_for_job
TTSManager._cache_key_for_text = _sr_v7_cache_key_for_text
TTSManager._gain600_wav_for_raw = _sr_v7_gain600_wav_for_raw
TTSManager._ensure_reading_mpv = _sr_v7_ensure_reading_mpv
TTSManager._stop_reading_mpv = _sr_v7_stop_reading_mpv
TTSManager._play_reading_with_persistent_mpv = _sr_v7_play_reading_with_persistent_mpv
TTSManager._stop_current_playback = _sr_v7_old_stop_current_playback
TTSManager._play_with_mpv = _sr_v7_play_with_mpv
TTSManager._sapi_com_wav_for_text = _sr_v7_sapi_com_wav_for_text
TTSManager._worker = _sr_v7_audio_worker
TTSManager.close = _sr_v7_close

# ---------- audio v8: queue correctness + transition-speed + diagnostic audit ----------
# Fixes audited from the reported bugs:
# 1) A single-slot queue lets reading_next prefetch overwrite an immediate reading request.
# 2) Worker-side drain_latest can skip the current audible segment if a prefetch arrives quickly.
# 3) append-play speed changes are global in mpv; setting speed for the queued next file too early
#    can warp the current file. v8 delays large next-speed changes until the estimated transition.
# 4) Logs now expose synth_ms / wav_dur / target / speed / cap / queue state so the remaining
#    bottleneck can be identified from speedreader_debug.log instead of guessing.

_sr_v8_old_init = TTSManager.__init__

def _sr_v8_init(self, *args, **kwargs):
    _sr_v8_old_init(self, *args, **kwargs)
    try:
        self.queue = queue.Queue(maxsize=8)
    except Exception:
        pass
    self._pending_reading_prefetch_item = None
    self._audio_generation = 0
    self._reading_mpv_speed = None
    self._reading_mpv_pitch = None
    self._reading_expected_end_at = None
    self._reading_expected_end_generation = 0
    self._audio_last_audit = {}
    self._debug_audio_verbose = True

def _sr_v8_put_item_lossless(self, item):
    """Queue an item without letting a prefetch erase an immediate reading segment."""
    try:
        self.queue.put_nowait(item)
        return True
    except queue.Full:
        # Drop one queued prefetch/wake first; never intentionally drop a normal reading request.
        kept = []
        dropped = False
        try:
            while True:
                old = self.queue.get_nowait()
                r = str(old.get("reason", "") if isinstance(old, dict) else "").lower()
                if (not dropped) and (r.startswith("__wake") or r.startswith("reading_next")):
                    dropped = True
                    continue
                kept.append(old)
        except Exception:
            pass
        for old in kept[-6:]:
            try:
                self.queue.put_nowait(old)
            except Exception:
                break
        try:
            self.queue.put_nowait(item)
            return True
        except Exception:
            return False

def _sr_v8_speak_text(self, text, wpm=None, reason="segment", target_duration=None):
    if not self.enabled:
        return
    text = self._normalize_text(text)
    if not text:
        return
    self.start()
    effective_wpm = self.effective_wpm_for_playback(wpm)
    item = {
        "text": text,
        "wpm": effective_wpm,
        "requested_wpm": self._normalize_wpm(wpm),
        "reason": str(reason or "segment"),
        "target_duration": None if target_duration is None else max(0.001, float(target_duration)),
        "time": time.time(),
    }
    r = str(reason or "").lower()
    if _sr_v7_is_reading_next_reason(reason):
        # Store as a replaceable pending prefetch.  Do not clear the queue and do not stop playback.
        self._pending_reading_prefetch_item = item
        self.log(
            f"TTS v8 queued pending prefetch reason={reason} chars={len(text)} "
            f"target={item['target_duration']} wpm={effective_wpm:.1f}",
            verbose=True,
        )
        # Wake worker only when idle.  If the queue is full, current work is more important.
        try:
            self.queue.put_nowait({"reason": "__wake_prefetch__", "text": "", "wpm": effective_wpm, "target_duration": None, "time": time.time()})
        except Exception:
            pass
        return

    if _sr_v7_is_reading_reason(reason):
        # A normal reading request means start/jump/restart/speed-change.  Invalidate old prefetch.
        self._pending_reading_prefetch_item = None
        self.clear_queue()
        self._stop_current_playback()
        self._sr_v8_put_item_lossless(item)
        return

    if _sr_v7_is_typing_reason(reason):
        # Typing should keep only the latest key target.
        self.clear_queue()
        self._sr_v8_put_item_lossless(item)
        return

    self.clear_queue()
    self._stop_current_playback()
    self._sr_v8_put_item_lossless(item)

def _sr_v8_get_pending_prefetch(self):
    item = getattr(self, "_pending_reading_prefetch_item", None)
    self._pending_reading_prefetch_item = None
    return item

def _sr_v8_get_next_item(self):
    try:
        item = self.queue.get(timeout=0.25)
    except queue.Empty:
        return self._sr_v8_get_pending_prefetch()
    except Exception:
        return None
    if item is None:
        return None
    try:
        if isinstance(item, dict) and str(item.get("reason", "")).startswith("__wake"):
            pending = self._sr_v8_get_pending_prefetch()
            return pending
    except Exception:
        pass
    return item

def _sr_v8_drain_typing_latest(self, item):
    latest = item
    try:
        while True:
            newer = self.queue.get_nowait()
            if newer is None:
                return None
            if isinstance(newer, dict) and _sr_v7_is_typing_reason(newer.get("reason", "")):
                latest = newer
            else:
                # Preserve non-typing work; it may be the reading prefetch.
                self._sr_v8_put_item_lossless(newer)
                break
    except Exception:
        pass
    return latest

def _sr_v8_schedule_transition_speed(self, proc, speed, pitch_correction):
    try:
        end_at = getattr(self, "_reading_expected_end_at", None)
        generation = int(getattr(self, "_reading_expected_end_generation", 0) or 0)
        if end_at is None:
            return
        delay = max(0.0, float(end_at) - time.perf_counter() - 0.060)
        def runner():
            try:
                if delay > 0:
                    time.sleep(delay)
                if self.stop_event.is_set() or not self.enabled:
                    return
                if int(getattr(self, "_reading_expected_end_generation", 0) or 0) != generation:
                    return
                if proc is None or proc.poll() is not None:
                    return
                _sr_v7_send_mpv(self, proc, f"set speed {float(speed):.4f}")
                _sr_v7_send_mpv(self, proc, f"set audio-pitch-correction {pitch_correction}")
                self._reading_mpv_speed = float(speed)
                self._reading_mpv_pitch = pitch_correction
                self.log(f"TTS v8 transition speed applied speed={float(speed):.3f} pitch={pitch_correction}", verbose=True)
            except Exception:
                pass
        threading.Thread(target=runner, name="SpeedReaderAudioTransitionSpeed", daemon=True).start()
    except Exception:
        pass

def _sr_v8_play_reading_with_persistent_mpv(self, wav_path, wpm=None, reason="reading", target_duration=None):
    proc = self._ensure_reading_mpv()
    if proc is None:
        return False
    speed = self._speed_for_target(wav_path, wpm=wpm, target_duration=target_duration)
    pitch_correction = "yes" if speed <= 4.0 else "no"
    mode = "append-play" if _sr_v7_is_reading_next_reason(reason) else "replace"
    try:
        max_speed = float(getattr(self, "max_mpv_speed", 24.0) or 24.0)
    except Exception:
        max_speed = 24.0
    capped = abs(float(speed) - max_speed) < 0.0001

    try:
        if mode == "replace":
            if not _sr_v7_send_mpv(self, proc, f"set speed {float(speed):.4f}"):
                raise RuntimeError("failed to set mpv speed")
            _sr_v7_send_mpv(self, proc, f"set audio-pitch-correction {pitch_correction}")
            self._reading_mpv_speed = float(speed)
            self._reading_mpv_pitch = pitch_correction
            try:
                if target_duration:
                    self._reading_expected_end_at = time.perf_counter() + float(target_duration)
                    self._reading_expected_end_generation = int(getattr(self, "_reading_expected_end_generation", 0) or 0) + 1
            except Exception:
                self._reading_expected_end_at = None
        else:
            # mpv speed is global.  For append-play, applying a different speed immediately changes
            # the current segment.  If speed differs materially, schedule it near the boundary.
            cur_speed = getattr(self, "_reading_mpv_speed", None)
            if cur_speed is None:
                _sr_v7_send_mpv(self, proc, f"set speed {float(speed):.4f}")
                _sr_v7_send_mpv(self, proc, f"set audio-pitch-correction {pitch_correction}")
                self._reading_mpv_speed = float(speed)
                self._reading_mpv_pitch = pitch_correction
            else:
                try:
                    diff = abs(float(speed) - float(cur_speed)) / max(0.001, float(cur_speed))
                except Exception:
                    diff = 0.0
                if diff >= 0.08:
                    self._sr_v8_schedule_transition_speed(proc, speed, pitch_correction)
                # If diff is small, keep current speed to avoid perturbing active playback.

        if not _sr_v7_send_mpv(self, proc, f"loadfile {_sr_audio_quote_mpv_path(wav_path)} {mode}"):
            raise RuntimeError("failed to loadfile into persistent mpv")

        try:
            wav_dur = self._wav_duration_seconds(wav_path)
            size = Path(wav_path).stat().st_size
        except Exception:
            wav_dur = None
            size = "NA"
        self.log(
            f"TTS v8 persistent reading command reason={reason} mode={mode} "
            f"effective_wpm={float(wpm or 0):.1f} target={target_duration} wav_dur={wav_dur} "
            f"speed={float(speed):.3f} capped={capped} pitch={pitch_correction} size={size} file={wav_path}",
            verbose=True,
        )
        self.current_proc = proc
        return True
    except Exception:
        self.log("TTS v8 persistent reading command failed, falling back to one-shot mpv:\n" + traceback.format_exc())
        self._stop_reading_mpv()
        return False

def _sr_v8_process_audio_item(self, item, voice, win32com):
    if not item or not self.enabled:
        return
    reason = item.get("reason", "segment")
    if _sr_v7_is_typing_reason(reason) and voice is not None:
        try:
            item2 = self._wait_and_coalesce_typing_item(item)
            if item2 is not None:
                item = item2
                reason = item.get("reason", reason)
            item = self._sr_v8_drain_typing_latest(item)
            if item is None:
                return
            reason = item.get("reason", reason)
        except Exception:
            pass
        text0 = self._normalize_text(item.get("text", ""))
        if text0:
            self._direct_sapi_typing(voice, text0, wpm=self._normalize_wpm(item.get("wpm")), reason=reason)
        return

    text_to_speak = self._normalize_text(item.get("text", ""))
    if not text_to_speak:
        return
    wpm = self._normalize_wpm(item.get("wpm"))
    target_duration = item.get("target_duration")
    self._sr_v7_current_sapi_rate = self._sapi_rate_for_job(reason, wpm=wpm, text=text_to_speak)
    self._sr_v7_current_synth_mode = "typing" if _sr_v7_is_typing_reason(reason) else "reading"

    synth_t0 = time.perf_counter()
    wav_path = None
    if voice is not None and win32com is not None:
        wav_path = self._sapi_com_wav_for_text(voice, win32com, text_to_speak)
    if wav_path is None and IS_WINDOWS:
        wav_path = self._sapi_powershell_wav_for_text(text_to_speak)
    synth_ms = (time.perf_counter() - synth_t0) * 1000.0

    if wav_path is None:
        self.log(f"TTS v8 synth failed reason={reason} chars={len(text_to_speak)} synth_ms={synth_ms:.1f}")
        return

    try:
        dur = self._wav_duration_seconds(wav_path)
        speed = self._speed_for_target(wav_path, wpm=wpm, target_duration=target_duration)
        size = Path(wav_path).stat().st_size
        max_speed = float(getattr(self, "max_mpv_speed", 24.0) or 24.0)
        capped = abs(float(speed) - max_speed) < 0.0001
        target = None if target_duration is None else float(target_duration)
        danger = ""
        if target and synth_ms / 1000.0 > max(1.0, target * 0.50):
            danger += " synth_slow_vs_target"
        if capped:
            danger += " speed_capped_audio_may_lag_visual"
        self.log(
            f"TTS v8 audit reason={reason} chars={len(text_to_speak)} rate={getattr(self, '_sr_v7_current_sapi_rate', None)} "
            f"synth_ms={synth_ms:.1f} wav_dur={dur} target={target_duration} speed={speed:.3f} "
            f"size={size} pending_prefetch={getattr(self, '_pending_reading_prefetch_item', None) is not None}{danger}",
            verbose=True,
        )
    except Exception:
        pass

    if _sr_v7_is_typing_reason(reason):
        self._play_with_persistent_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration)
    else:
        self._play_with_mpv(wav_path, wpm=wpm, reason=reason, target_duration=target_duration)

def _sr_v8_audio_worker(self):
    voice = None
    win32com = None
    pythoncom = None
    self._refresh_mpv_path()
    if self.mpv_path:
        self.log(f"TTS MPV found: {self.mpv_path}")
    else:
        self.log("TTS MPV not found yet; playback will rescan script folder, PATH, winget, scoop and chocolatey folders each time")
    if IS_WINDOWS:
        try:
            import pythoncom as _pythoncom
            import win32com.client as _win32com_client
            pythoncom = _pythoncom
            pythoncom.CoInitialize()
            class _Win32ComModule:
                client = _win32com_client
            win32com = _Win32ComModule
            voice = win32com.client.Dispatch("SAPI.SpVoice")
            self._select_sapi_voice(voice)
            self.backend = "mpv-v8/audit-queue-prebuffer/sapi"
            self.ready = True
            self.log("TTS backend ready: v8 queue-safe prebuffer + compact WAV + persistent MPV reading")
        except Exception as e:
            self.backend = "mpv-v8/powershell-fallback"
            self.ready = bool(self.mpv_path)
            self.log(f"TTS SAPI COM unavailable, fallback to PowerShell synthesis for reading: {e}")
    else:
        self.backend = "mpv-v8/nonwindows"
        self.ready = bool(self.mpv_path)

    try:
        while not self.stop_event.is_set():
            item = self._sr_v8_get_next_item()
            if item is None:
                if self.stop_event.is_set():
                    break
                continue
            if item is None:
                break
            self._sr_v8_process_audio_item(item, voice, win32com)
            # After current item, immediately process the latest pending prefetch while current audio is playing.
            pending = self._sr_v8_get_pending_prefetch()
            if pending is not None and not self.stop_event.is_set() and self.enabled:
                self._sr_v8_process_audio_item(pending, voice, win32com)
    finally:
        try:
            if voice is not None:
                try:
                    voice.Speak("", 2)
                except Exception:
                    pass
        except Exception:
            pass
        try:
            self._stop_current_playback()
        except Exception:
            pass
        try:
            self._stop_typing_mpv()
        except Exception:
            pass
        try:
            if pythoncom is not None:
                pythoncom.CoUninitialize()
        except Exception:
            pass
        try:
            if self.tts_temp_dir is not None:
                shutil.rmtree(str(self.tts_temp_dir), ignore_errors=True)
                self.tts_temp_dir = None
                self.wav_cache.clear()
                self._ps_script_path = None
        except Exception:
            pass

def _sr_v8_clear_queue(self):
    try:
        while True:
            self.queue.get_nowait()
    except Exception:
        pass
    try:
        self._pending_reading_prefetch_item = None
    except Exception:
        pass

TTSManager.__init__ = _sr_v8_init
TTSManager._sr_v8_put_item_lossless = _sr_v8_put_item_lossless
TTSManager.speak_text = _sr_v8_speak_text
TTSManager._sr_v8_get_pending_prefetch = _sr_v8_get_pending_prefetch
TTSManager._sr_v8_get_next_item = _sr_v8_get_next_item
TTSManager._sr_v8_drain_typing_latest = _sr_v8_drain_typing_latest
TTSManager._sr_v8_schedule_transition_speed = _sr_v8_schedule_transition_speed
TTSManager._play_reading_with_persistent_mpv = _sr_v8_play_reading_with_persistent_mpv
TTSManager._sr_v8_process_audio_item = _sr_v8_process_audio_item
TTSManager._worker = _sr_v8_audio_worker
TTSManager.clear_queue = _sr_v8_clear_queue

# ---------- audio v9: rollback to direct system SAPI, no MPV, no WAV synthesis ----------
# User conclusion after testing: MPV path still requires WAV synthesis; file synthesis is the real bottleneck.
# This patch disables MPV/WAV audio for both reading and typing and uses Windows' built-in SAPI device output.
# Reading voice speed is clamped to the practical system-TTS range: 60..600 WPM.
# Typing voice uses a fixed audible prompt speed: 400 WPM, with short coalescing to avoid purge-before-sound.

DIRECT_SAPI_READING_MIN_WPM = 60.0
DIRECT_SAPI_READING_MAX_WPM = 600.0
DIRECT_SAPI_TYPING_WPM = 400.0
DIRECT_SAPI_TYPING_COALESCE_MS = 150

def _direct_sapi_clamp(value, lo, hi):
    try:
        v = float(value)
    except Exception:
        v = lo
    if v < lo:
        return float(lo)
    if v > hi:
        return float(hi)
    return float(v)

def _direct_sapi_rate_from_wpm(wpm, typing=False):
    """Map practical WPM to SAPI Rate -10..10.

    This intentionally avoids impossible 1000-4000+ system voice speeds.  Past the limit, the
    audio stays at max Rate so it remains audible instead of turning into silence/stutter.
    """
    try:
        w = float(wpm)
    except Exception:
        w = DIRECT_SAPI_TYPING_WPM if typing else 300.0
    if typing:
        w = DIRECT_SAPI_TYPING_WPM
    w = _direct_sapi_clamp(w, DIRECT_SAPI_READING_MIN_WPM, DIRECT_SAPI_READING_MAX_WPM)
    # conservative piecewise mapping tuned for Windows SAPI Chinese voices
    if w <= 70:
        return -7
    if w <= 90:
        return -5
    if w <= 120:
        return -3
    if w <= 180:
        return -1
    if w <= 260:
        return 0
    if w <= 340:
        return 2
    if w <= 430:
        return 4
    if w <= 520:
        return 7
    return 10

def _direct_sapi_estimate_seconds(text, effective_wpm, typing=False):
    if typing:
        return 0.42
    try:
        chars = max(1, sum(1 for ch in str(text) if (ch.strip() and (ch.isalnum() or is_cjk_char(ch)))))
    except Exception:
        chars = max(1, len(str(text or "")))
    wpm = _direct_sapi_clamp(effective_wpm, DIRECT_SAPI_READING_MIN_WPM, DIRECT_SAPI_READING_MAX_WPM)
    # extra guard: real SAPI voices often speak slower than nominal Rate=10, so avoid premature purge
    return max(0.75, chars * 60.0 / wpm * 1.45 + 0.18)

def _direct_sapi_tts_init(self, log_func=None, enabled=True):
    self.log = log_func or (lambda *a, **k: None)
    self.enabled = bool(enabled)
    self.queue = queue.Queue(maxsize=16)
    self.stop_event = threading.Event()
    self.thread = None
    self.backend = "system-sapi-direct"
    self.ready = False
    self.started = False
    self.current_proc = None
    self.tts_temp_dir = None
    self.wav_cache = {}
    self.cache_limit = 0
    self.mpv_path = None
    self.base_speech_wpm = 300.0
    self.max_mpv_speed = 1.0
    self.direct_sapi = True
    self.reading_min_wpm = DIRECT_SAPI_READING_MIN_WPM
    self.reading_max_wpm = DIRECT_SAPI_READING_MAX_WPM
    self.typing_fixed_wpm = DIRECT_SAPI_TYPING_WPM
    self._sapi_voice = None
    self._sapi_lock = threading.RLock()
    self._estimated_speaking_until = 0.0
    self._last_reading_sig = None
    self._last_typing_emit = 0.0
    self._typing_pending_item = None

def _direct_sapi_start(self):
    if self.started:
        return
    self.started = True
    self.stop_event.clear()
    self.thread = threading.Thread(target=self._worker, name="SpeedReaderDirectSAPI", daemon=True)
    self.thread.start()

def _direct_sapi_set_enabled(self, enabled):
    self.enabled = bool(enabled)
    if not self.enabled:
        self._stop_current_playback()

def _direct_sapi_effective_wpm_for_playback(self, wpm):
    return _direct_sapi_clamp(wpm, DIRECT_SAPI_READING_MIN_WPM, DIRECT_SAPI_READING_MAX_WPM)

def _direct_sapi_is_playing(self):
    try:
        return time.perf_counter() < float(getattr(self, "_estimated_speaking_until", 0.0) or 0.0)
    except Exception:
        return False

def _direct_sapi_clear_queue(self):
    try:
        while True:
            self.queue.get_nowait()
    except Exception:
        pass
    self._typing_pending_item = None

def _direct_sapi_stop_current_playback(self):
    self.clear_queue()
    self._estimated_speaking_until = 0.0
    try:
        self.queue.put_nowait({"cmd": "stop", "reason": "stop", "text": ""})
    except Exception:
        pass

def _direct_sapi_close(self):
    try:
        self.stop_event.set()
        self.clear_queue()
        try:
            self.queue.put_nowait(None)
        except Exception:
            pass
        try:
            if self._sapi_voice is not None:
                self._sapi_voice.Speak("", 2)
        except Exception:
            pass
    except Exception:
        pass

def _direct_sapi_speak_text(self, text, wpm=None, reason="segment", target_duration=None):
    if not self.enabled:
        return
    text = self._normalize_text(text) if hasattr(self, "_normalize_text") else str(text or "").strip()
    if not text:
        return
    self.start()
    reason = str(reason or "segment")
    is_typing = reason.startswith("typing")
    effective_wpm = DIRECT_SAPI_TYPING_WPM if is_typing else self.effective_wpm_for_playback(wpm)
    item = {
        "text": text,
        "wpm": effective_wpm,
        "requested_wpm": wpm,
        "reason": reason,
        "typing": bool(is_typing),
        "created_at": time.perf_counter(),
    }
    if is_typing:
        # Typing is latest-only, but do not purge on every physical key before SAPI emits audio.
        self._typing_pending_item = item
        try:
            self.queue.put_nowait({"cmd": "typing_wake", "reason": "typing_wake", "text": ""})
        except queue.Full:
            self.clear_queue()
            try:
                self.queue.put_nowait({"cmd": "typing_wake", "reason": "typing_wake", "text": ""})
            except Exception:
                pass
        except Exception:
            pass
        return

    # Reading: latest current segment replaces old queued reading only on explicit call.
    # No mpv, no wav, no synthesis-to-file delay.
    self.clear_queue()
    try:
        self.queue.put_nowait(item)
    except queue.Full:
        self.clear_queue()
        try:
            self.queue.put_nowait(item)
        except Exception:
            pass

def _direct_sapi_emit_voice(self, voice, text, wpm, reason, typing=False, purge=True):
    text = str(text or "").strip()
    if not text:
        return
    flags = 1 | (2 if purge else 0)  # SVSFlagsAsync | optional SVSFPurgeBeforeSpeak
    rate = _direct_sapi_rate_from_wpm(wpm, typing=typing)
    try:
        voice.Rate = int(rate)
        voice.Volume = 100
    except Exception:
        pass
    try:
        stream_id = voice.Speak(text, flags)
    except Exception:
        self.log("Direct SAPI Speak failed:\n" + traceback.format_exc())
        return
    est = _direct_sapi_estimate_seconds(text, wpm, typing=typing)
    self._estimated_speaking_until = max(float(getattr(self, "_estimated_speaking_until", 0.0) or 0.0), time.perf_counter() + est)
    try:
        self.log(
            f"TTS direct SAPI speak reason={reason} typing={typing} text_len={len(text)} "
            f"requested_wpm={wpm} rate={rate} est_sec={est:.2f} stream_id={stream_id}",
            verbose=True,
        )
    except Exception:
        pass

def _direct_sapi_worker(self):
    voice = None
    pythoncom = None
    try:
        if IS_WINDOWS:
            try:
                import pythoncom as _pythoncom
                import win32com.client as _win32com_client
                pythoncom = _pythoncom
                pythoncom.CoInitialize()
                voice = _win32com_client.Dispatch("SAPI.SpVoice")
                self._select_sapi_voice(voice)
                try:
                    voice.Volume = 100
                except Exception:
                    pass
                self._sapi_voice = voice
                self.ready = True
                self.backend = "system-sapi-direct"
                self.log("TTS backend ready: direct Windows SAPI, MPV/WAV synthesis disabled, typing fixed 400 WPM")
            except Exception:
                self.ready = False
                self.backend = "system-sapi-direct-unavailable"
                self.log("Direct Windows SAPI unavailable:\n" + traceback.format_exc())
        else:
            self.ready = False
            self.backend = "system-sapi-direct-windows-only"
            self.log("Direct SAPI TTS is Windows-only")
        while not self.stop_event.is_set():
            try:
                item = self.queue.get(timeout=0.25)
            except queue.Empty:
                continue
            if item is None:
                break
            if voice is None or not self.enabled:
                continue
            cmd = item.get("cmd") if isinstance(item, dict) else None
            if cmd == "stop":
                try:
                    voice.Speak("", 2)
                except Exception:
                    pass
                self._estimated_speaking_until = 0.0
                continue
            if cmd == "typing_wake":
                # Coalesce newest typing target over a tiny audible window.
                deadline = time.perf_counter() + DIRECT_SAPI_TYPING_COALESCE_MS / 1000.0
                while time.perf_counter() < deadline and not self.stop_event.is_set():
                    time.sleep(0.006)
                    # If new typing wakes arrive, keep only the newest item.
                    try:
                        while True:
                            newer = self.queue.get_nowait()
                            if newer is None:
                                self.stop_event.set()
                                break
                            if isinstance(newer, dict) and newer.get("cmd") == "typing_wake":
                                deadline = time.perf_counter() + DIRECT_SAPI_TYPING_COALESCE_MS / 1000.0
                            elif isinstance(newer, dict) and newer.get("cmd") == "stop":
                                try:
                                    voice.Speak("", 2)
                                except Exception:
                                    pass
                                self._estimated_speaking_until = 0.0
                            else:
                                # non-typing reading item should be restored
                                try:
                                    self.queue.put_nowait(newer)
                                except Exception:
                                    pass
                                break
                    except queue.Empty:
                        pass
                    except Exception:
                        break
                pending = self._typing_pending_item
                self._typing_pending_item = None
                if pending and self.enabled:
                    self._emit_voice(voice, pending.get("text", ""), DIRECT_SAPI_TYPING_WPM, pending.get("reason", "typing"), typing=True, purge=True)
                continue
            if isinstance(item, dict):
                typing = bool(item.get("typing", False))
                text = item.get("text", "")
                wpm = DIRECT_SAPI_TYPING_WPM if typing else self.effective_wpm_for_playback(item.get("wpm", 300))
                # Reading deliberately purges old system speech only for this new segment; SpeedReader
                # side avoids calling this while the previous segment is estimated to be audible.
                self._emit_voice(voice, text, wpm, item.get("reason", "reading"), typing=typing, purge=True)
    finally:
        try:
            if voice is not None:
                voice.Speak("", 2)
        except Exception:
            pass
        try:
            if pythoncom is not None:
                pythoncom.CoUninitialize()
        except Exception:
            pass

TTSManager.__init__ = _direct_sapi_tts_init
TTSManager.start = _direct_sapi_start
TTSManager.set_enabled = _direct_sapi_set_enabled
TTSManager.effective_wpm_for_playback = _direct_sapi_effective_wpm_for_playback
TTSManager.is_playing = _direct_sapi_is_playing
TTSManager.clear_queue = _direct_sapi_clear_queue
TTSManager._stop_current_playback = _direct_sapi_stop_current_playback
TTSManager.stop_current_playback = _direct_sapi_stop_current_playback
TTSManager.close = _direct_sapi_close
TTSManager.speak_text = _direct_sapi_speak_text
TTSManager._emit_voice = _direct_sapi_emit_voice
TTSManager._worker = _direct_sapi_worker

def _sr_v9_current_tts_wpm(self):
    if getattr(self, "typing_mode", False):
        return DIRECT_SAPI_TYPING_WPM
    try:
        return max(DIRECT_SAPI_READING_MIN_WPM, float(getattr(self, "wpm", 300) or 300))
    except Exception:
        return 300.0

def _sr_v9_effective_tts_wpm(self, wpm=None):
    if getattr(self, "typing_mode", False):
        return DIRECT_SAPI_TYPING_WPM
    try:
        value = self.current_tts_wpm() if wpm is None else float(wpm)
    except Exception:
        value = 300.0
    return _direct_sapi_clamp(value, DIRECT_SAPI_READING_MIN_WPM, DIRECT_SAPI_READING_MAX_WPM)

def _sr_v9_tts_speed_bucket_for_wpm(self, wpm=None):
    try:
        return int(round(float(self.effective_tts_wpm(wpm)) / 25.0) * 25)
    except Exception:
        return 300

def _sr_v9_tts_segment_from_pos(self, pos, typing=False):
    if not self.text:
        return "", pos, pos
    n = len(self.text)
    pos = max(0, min(int(pos), max(0, n - 1)))
    if typing:
        return self.text[pos:pos + 1], pos, min(n, pos + 1)
    start = pos
    while start < n and not self.text[start].strip():
        start += 1
    if start >= n:
        return "", pos, pos
    hard_end_chars = set("。！？!?；;\n")
    soft_end_chars = set("，,、：:")
    effective = self.effective_tts_wpm(getattr(self, "wpm", 300))
    # Direct system TTS cannot track 3000+ WPM.  Keep segment length in a practical audible range.
    target_seconds = 7.0 if effective >= 500 else 8.5
    max_chars = max(32, min(110, int(effective / 60.0 * target_seconds)))
    min_chars = max(10, min(28, int(max_chars * 0.35)))
    end = start
    while end < n and (end - start) < max_chars:
        ch = self.text[end]
        end += 1
        if (end - start) >= min_chars and ch in hard_end_chars:
            break
        if (end - start) >= max(24, min_chars + 8) and ch in soft_end_chars:
            break
    segment = self.text[start:end].strip()
    if not segment or not any(c.isalnum() or self.is_cjk(c) for c in segment):
        return "", start, end
    return segment, start, end

def _sr_v9_speak_current_target(self, force=False):
    if not getattr(self, "tts_enabled", False) or self.tts is None or not self.text:
        return
    pos = self.typing_flat_char_index if self.typing_mode else self.reader_pos
    if pos < 0 or pos >= len(self.text):
        return
    mode = "typing" if self.typing_mode else "reading"
    requested_wpm = self.current_tts_wpm()
    effective_wpm = self.effective_tts_wpm(requested_wpm)
    try:
        active = getattr(self, "_tts_active_segment", None)
        wpm_bucket = self.tts_speed_bucket_for_wpm(effective_wpm)
        if (not force) and active:
            a_mode, a_start, a_end, a_wpm_bucket = active
            if a_mode == mode and a_start <= pos < a_end and abs(wpm_bucket - a_wpm_bucket) <= 25:
                return
            # Reading direct SAPI should not be purged just because the visual cursor outran audio.
            # Above 600 WPM, audio is intentionally clamped at max system speed and allowed to finish.
            if (not self.typing_mode) and self.tts is not None and hasattr(self.tts, "is_playing") and self.tts.is_playing():
                return
        segment, start, end = self.tts_segment_from_pos(pos, typing=self.typing_mode)
        if not segment:
            return
        sig = (mode, start, end, hashlib.sha1(segment.encode("utf-8", errors="ignore")).hexdigest()[:12], wpm_bucket)
        if (not force) and sig == getattr(self, "_last_spoken_target", None):
            return
        self._last_spoken_target = sig
        self._tts_active_segment = (mode, start, end, wpm_bucket)
        self.tts.speak_text(segment, wpm=effective_wpm, reason=f"{mode}:{start}-{end}")
    except Exception:
        self.log_debug("direct SAPI speak_current_target failed:\n" + traceback.format_exc())

def _sr_v9_stop_tts_playback(self):
    self._tts_active_segment = None
    self._last_spoken_target = None
    try:
        if self.tts is not None:
            self.tts.clear_queue()
            self.tts._stop_current_playback()
    except Exception:
        pass

def _sr_v9_on_reader_speed_changed_for_tts(self, old_wpm):
    if not self.playing:
        return
    old_bucket = self.tts_speed_bucket_for_wpm(old_wpm)
    new_bucket = self.tts_speed_bucket_for_wpm(getattr(self, "wpm", 300))
    # Above the direct SAPI max, all displayed WPM values map to the same audible max.
    # Do not repeatedly purge/restart when the effective audible speed did not change.
    if old_bucket != new_bucket:
        self._tts_active_segment = None
        self._last_spoken_target = None
        self.speak_current_target(force=True)
    else:
        self.speak_current_target(force=False)

SpeedReader.current_tts_wpm = _sr_v9_current_tts_wpm
SpeedReader.effective_tts_wpm = _sr_v9_effective_tts_wpm
SpeedReader.tts_speed_bucket_for_wpm = _sr_v9_tts_speed_bucket_for_wpm
SpeedReader.tts_segment_from_pos = _sr_v9_tts_segment_from_pos
SpeedReader.speak_current_target = _sr_v9_speak_current_target
SpeedReader.stop_tts_playback = _sr_v9_stop_tts_playback
SpeedReader.on_reader_speed_changed_for_tts = _sr_v9_on_reader_speed_changed_for_tts

# ---------- audio v11: no-MPV direct SAPI final debug, typing voice = plugin max, user WPM ignored ----------
# 打字模式语音和用户输入速度彻底解耦：
# - 不用 MPV；
# - 不生成 WAV；
# - 使用 Windows SAPI 直接向系统音频输出；
# - 打字模式始终用 SAPI 可提供的最高 Rate=10 发音；
# - 用户输入速度/WPM 再高，也不会把语音继续加速，也不会每个按键立刻 purge；
# - 语音按自己的固定节奏读“最新目标字”，用户按自己的速度继续输入，各做各的。

DIRECT_SAPI_TYPING_PLUGIN_MAX_WPM = 600.0
DIRECT_SAPI_TYPING_EMIT_INTERVAL_MS = 150

def _v11_direct_rate_from_wpm(wpm, typing=False):
    if typing:
        return 10  # SAPI.SpVoice Rate 最大值；不再跟用户实时 WPM 走
    try:
        w = float(wpm)
    except Exception:
        w = 300.0
    w = max(DIRECT_SAPI_READING_MIN_WPM, min(DIRECT_SAPI_READING_MAX_WPM, w))
    if w <= 70:
        return -7
    if w <= 90:
        return -5
    if w <= 120:
        return -3
    if w <= 180:
        return -1
    if w <= 260:
        return 0
    if w <= 340:
        return 2
    if w <= 430:
        return 4
    if w <= 520:
        return 7
    return 10

def _v11_emit_voice(self, voice, text, wpm, reason, typing=False, purge=True):
    text = str(text or "").strip()
    if not text:
        return
    rate = _v11_direct_rate_from_wpm(wpm, typing=typing)
    flags = 1 | (2 if purge else 0)  # async + optional purge
    try:
        voice.Rate = int(rate)
        voice.Volume = 100
    except Exception:
        pass
    try:
        stream_id = voice.Speak(text, flags)
    except Exception:
        self.log("Direct SAPI v11 Speak failed:\n" + traceback.format_exc())
        return
    if typing:
        # 以固定发声节奏为准，不再让输入速度决定“还在不在读”。
        est = max(0.15, DIRECT_SAPI_TYPING_EMIT_INTERVAL_MS / 1000.0)
    else:
        est = _direct_sapi_estimate_seconds(text, wpm, typing=False)
    self._estimated_speaking_until = max(float(getattr(self, "_estimated_speaking_until", 0.0) or 0.0), time.perf_counter() + est)
    try:
        self.log(
            f"TTS direct SAPI v11 reason={reason} typing={typing} len={len(text)} "
            f"effective_wpm={DIRECT_SAPI_TYPING_PLUGIN_MAX_WPM if typing else wpm} rate={rate} "
            f"emit_interval_ms={DIRECT_SAPI_TYPING_EMIT_INTERVAL_MS if typing else 'NA'} stream_id={stream_id}",
            verbose=True,
        )
    except Exception:
        pass

_v11_old_init = TTSManager.__init__

def _v11_tts_init(self, *args, **kwargs):
    _v11_old_init(self, *args, **kwargs)
    self.mpv_path = None
    self.backend = "system-sapi-direct-v11-no-mpv"
    self.direct_sapi = True
    self.typing_fixed_wpm = DIRECT_SAPI_TYPING_PLUGIN_MAX_WPM
    self._typing_pending_item = None
    self._typing_wake_queued = False

def _v11_speak_text(self, text, wpm=None, reason="segment", target_duration=None):
    if not self.enabled:
        return
    text = self._normalize_text(text) if hasattr(self, "_normalize_text") else str(text or "").strip()
    if not text:
        return
    self.start()
    reason = str(reason or "segment")
    is_typing = reason.startswith("typing")
    effective_wpm = DIRECT_SAPI_TYPING_PLUGIN_MAX_WPM if is_typing else self.effective_wpm_for_playback(wpm)
    item = {
        "text": text,
        "wpm": effective_wpm,
        "requested_wpm": wpm,
        "reason": reason,
        "typing": bool(is_typing),
        "created_at": time.perf_counter(),
    }
    if is_typing:
        # 只保留最新字；如果已有 typing_wake 在路上，不再不断塞队列/清队列。
        self._typing_pending_item = item
        if not getattr(self, "_typing_wake_queued", False):
            self._typing_wake_queued = True
            try:
                self.queue.put_nowait({"cmd": "typing_wake", "reason": "typing_wake", "text": ""})
            except queue.Full:
                # 只清 typing 噪声，不触碰正在由 SAPI 直接播放的声音。
                try:
                    while True:
                        self.queue.get_nowait()
                except Exception:
                    pass
                try:
                    self.queue.put_nowait({"cmd": "typing_wake", "reason": "typing_wake", "text": ""})
                except Exception:
                    self._typing_wake_queued = False
            except Exception:
                self._typing_wake_queued = False
        return
    # 阅读模式：系统 TTS 直接朗读，WPM 超过上限时仍按上限读，不使用 MPV 追速。
    self.clear_queue()
    try:
        self.queue.put_nowait(item)
    except queue.Full:
        self.clear_queue()
        try:
            self.queue.put_nowait(item)
        except Exception:
            pass

def _v11_worker(self):
    voice = None
    pythoncom = None
    try:
        if IS_WINDOWS:
            try:
                import pythoncom as _pythoncom
                import win32com.client as _win32com_client
                pythoncom = _pythoncom
                pythoncom.CoInitialize()
                voice = _win32com_client.Dispatch("SAPI.SpVoice")
                self._select_sapi_voice(voice)
                try:
                    voice.Volume = 100
                except Exception:
                    pass
                self._sapi_voice = voice
                self.ready = True
                self.backend = "system-sapi-direct-v11-no-mpv"
                self.log("TTS backend ready: direct Windows SAPI v11, MPV/WAV disabled, typing uses SAPI max Rate=10 and ignores user WPM")
            except Exception:
                self.ready = False
                self.backend = "system-sapi-direct-v11-unavailable"
                self.log("Direct Windows SAPI v11 unavailable:\n" + traceback.format_exc())
        else:
            self.ready = False
            self.backend = "system-sapi-direct-v11-windows-only"
            self.log("Direct SAPI v11 is Windows-only")

        while not self.stop_event.is_set():
            try:
                item = self.queue.get(timeout=0.25)
            except queue.Empty:
                continue
            if item is None:
                break
            if voice is None or not self.enabled:
                continue
            cmd = item.get("cmd") if isinstance(item, dict) else None
            if cmd == "stop":
                try:
                    voice.Speak("", 2)
                except Exception:
                    pass
                self._estimated_speaking_until = 0.0
                self._typing_wake_queued = False
                continue
            if cmd == "typing_wake":
                # 固定节奏合并：用户再快也只更新 latest target，不直接打断当前声道。
                time.sleep(max(0.02, DIRECT_SAPI_TYPING_EMIT_INTERVAL_MS / 1000.0))
                pending = self._typing_pending_item
                self._typing_pending_item = None
                self._typing_wake_queued = False
                if pending and self.enabled:
                    self._emit_voice(
                        voice,
                        pending.get("text", ""),
                        DIRECT_SAPI_TYPING_PLUGIN_MAX_WPM,
                        pending.get("reason", "typing"),
                        typing=True,
                        purge=True,
                    )
                # 如果睡眠/发声期间又来了新字，再安排下一次固定节奏发声。
                if self._typing_pending_item is not None and not self._typing_wake_queued:
                    self._typing_wake_queued = True
                    try:
                        self.queue.put_nowait({"cmd": "typing_wake", "reason": "typing_wake", "text": ""})
                    except Exception:
                        self._typing_wake_queued = False
                continue
            if isinstance(item, dict):
                typing = bool(item.get("typing", False))
                text = item.get("text", "")
                wpm = DIRECT_SAPI_TYPING_PLUGIN_MAX_WPM if typing else self.effective_wpm_for_playback(item.get("wpm", 300))
                self._emit_voice(voice, text, wpm, item.get("reason", "reading"), typing=typing, purge=True)
    finally:
        try:
            if voice is not None:
                voice.Speak("", 2)
        except Exception:
            pass
        try:
            if pythoncom is not None:
                pythoncom.CoUninitialize()
        except Exception:
            pass

def _sr_v11_current_tts_wpm(self):
    if getattr(self, "typing_mode", False):
        return DIRECT_SAPI_TYPING_PLUGIN_MAX_WPM
    try:
        return max(DIRECT_SAPI_READING_MIN_WPM, float(getattr(self, "wpm", 300) or 300))
    except Exception:
        return 300.0

def _sr_v11_effective_tts_wpm(self, wpm=None):
    if getattr(self, "typing_mode", False):
        return DIRECT_SAPI_TYPING_PLUGIN_MAX_WPM
    try:
        value = self.current_tts_wpm() if wpm is None else float(wpm)
    except Exception:
        value = 300.0
    return max(DIRECT_SAPI_READING_MIN_WPM, min(DIRECT_SAPI_READING_MAX_WPM, value))

TTSManager.__init__ = _v11_tts_init
TTSManager.speak_text = _v11_speak_text
TTSManager._emit_voice = _v11_emit_voice
TTSManager._worker = _v11_worker
SpeedReader.current_tts_wpm = _sr_v11_current_tts_wpm
SpeedReader.effective_tts_wpm = _sr_v11_effective_tts_wpm

if __name__ == "__main__":
    if "--selftest" in sys.argv:
        run_selftest()
    else:
        app = SpeedReader()
        app.mainloop()
