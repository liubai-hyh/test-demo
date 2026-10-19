import tkinter as tk
import random
from PIL import Image, ImageTk
import json
import os
import time
import weakref  # 仅新增这1行，极简依赖
import subprocess  # 新增：用于启动外部程序（QQ音乐）
import platform   # 新增：用于判断操作系统（Windows/Mac）
import pyautogui  # <--- 新增：导入pyautogui（解决未解析引用）
import pygetwindow as gw  # <--- 可选：如果需要激活QQ音乐窗口，新增这行
# ========== 新增语音控制相关导入 ==========
import threading
import speech_recognition as sr
import pyttsx3
import requests
from aip import AipSpeech  # 百度官方SDK


# 全局宠物实例列表：存储所有正在运行的宠物对象
PET_INSTANCES = []
# 全局宠物GIF标识列表：用于唯一性校验（存储每个宠物的GIF路径组合哈希值）
PET_GIF_HASHES = []


class SmoothGifPet:
    def __init__(self, main_root, gif_path_list, angry_gif_path, pet_width=150, pet_height=180):
        # ========== 新增：QQ音乐唯一启动标记（默认未启动） ==========
        self.qq_music_launched = False  # <--- 4个空格（正确）
        # 以下所有最外层代码均缩进4个空格（正确：方法体层级）
        self.gif_combination_hash = self.calc_gif_combination_hash(gif_path_list, angry_gif_path)
        if len(PET_INSTANCES) >= 1 and self.gif_combination_hash in PET_GIF_HASHES:
            # if嵌套块：8个空格（正确：嵌套层级）
            print(f"警告：该宠物样式已存在，无法创建重复宠物！")
            # 显示提示气泡（临时窗口）
            tip_window = tk.Toplevel(main_root)
            tip_window.overrideredirect(True)
            tip_window.wm_attributes("-topmost", True)
            tk.Label(tip_window, text="该宠物样式已存在，无法重复创建！", bg="red", fg="white", padx=10, pady=5).pack()
            # 自动关闭提示窗口
            main_root.after(2000, tip_window.destroy)
            # 终止实例初始化
            self.is_alive = False
            return

        # 关键修改：使用Toplevel作为宠物窗口（避免多Tk冲突）
        self.root = tk.Toplevel(main_root)
        self.root.wm_attributes("-topmost", True)  # 强制宠物窗口置顶
        self.root.overrideredirect(True)
        self.is_topmost = True
        self.root.wm_attributes("-topmost", self.is_topmost)
        self.root.wm_attributes("-alpha", 1)

        # 自定义宠物尺寸（强制最小尺寸）
        self.pet_width = max(pet_width, 50)
        self.pet_height = max(pet_height, 60)

        # 实例有效性标记
        self.is_alive = True
        self.main_root = main_root  # 保存主窗口引用

        # ========== 新增：追逐互动相关参数 ==========
        self.is_chasing = False  # 是否正在追逐其他宠物
        self.is_being_chased = False  # 是否被其他宠物追逐
        self.target_pet = None  # 追逐目标
        self.chase_speed_multiplier = 1.5  # 追逐时速度倍率
        self.chase_distance_threshold = 200  # 触发追逐的距离阈值
        self.chase_cool_down = 5000  # 追逐冷却时间（避免频繁切换目标）
        self.last_chase_switch_time = time.time()  # 上次切换追逐目标的时间

        # 核心参数
        self.gif_path_list = gif_path_list
        self.angry_gif_path = angry_gif_path
        self.is_angry = False
        self.angry_duration = 3000
        self.angry_dialog_shown = False
        self.angry_dialog_cooldown = 1000

        # GIF播放参数
        self.current_gif_idx = 0
        self.gif_frames = []
        self.frame_delays = []
        self.current_frame_idx = 0
        self.preloaded_frames = {}
        self.is_gif_playing = True
        self.min_frame_delay = 16
        self.gif_animation_task = None

        # 自动移动参数
        self.base_move_speed_x = random.choice([3, 4, -3, -4])  # 基础移动速度（追逐时在此基础上倍率放大）
        self.base_move_speed_y = random.choice([3, 4, -3, -4])
        self.move_speed_x = self.base_move_speed_x
        self.move_speed_y = self.base_move_speed_y
        self.screen_width = self.main_root.winfo_screenwidth()
        self.screen_height = self.main_root.winfo_screenheight()
        self.is_auto_move = True
        self.move_task = None

        # 拖动参数
        self.is_dragging = False
        self.start_x = 0
        self.start_y = 0
        self.drag_threshold = 1
        self.move_offset_x = 0
        self.move_offset_y = 0
        self.start_x_root = 0
        self.start_y_root = 0
        self.win_start_x = 0
        self.win_start_y = 0
        self.drag_release_speed_x = 0
        self.drag_release_speed_y = 0
        self.inertia_coeff = 0.8
        self.damping_coeff = 0.95
        self.bounce_coeff = 0.8  # 强化碰撞：反弹系数（越大反弹力度越强）
        self.bounce_task = None

        # 互动参数
        self.config_path = "pet_config.json"
        self.is_random_behavior = False
        self.random_task_id = None
        self.last_operate_time = time.time()
        self.attention_wait_time = 10
        self.is_hide_mode = False
        self.bubble_duration = 3000
        self.is_bubble_showing = False
        self.bubble_hide_task = None
        # ========== 新增：喂食相关参数 ==========
        self.hunger_value = 50  # 饥饿值（0-100，0=极度饥饿，100=饱腹）
        self.hunger_down_speed = 1  # 每N秒饥饿值下降1点（可调整）
        self.feed_items = {  # 喂食道具配置（名称：恢复饥饿值）
            # 字典嵌套：8个空格（正确：嵌套层级）
            "普通猫粮": 20,
            "高级罐头": 50,
            "美味小鱼干": 80
        }
        self.is_feeding = False  # 是否正在喂食
        self.feed_cooldown = 2  # 喂食冷却时间（避免重复喂食，单位：秒）
        self.last_feed_time = 0  # 上次喂食时间
        self.hunger_check_task = None  # 饥饿值检测定时器

        # 台词词库（新增追逐相关台词）
        self.dialogue_lib = {
            # 字典嵌套：8个空格（正确：嵌套层级）
            "click": ["哎呀你戳到我啦~ 😝", "别摸我头啦~ 😳", "好痒呀~ 😆"],
            "double_click": ["双击我啦~ 🥰", "主人超爱我~ 😘", "太惊喜啦~ 🎉"],
            "attention": ["你不理我了~ 😟", "看看我嘛~ 🤗", "好无聊呀~ 😩"],
            "space": ["又被关注啦~ 🎉", "好开心~ 😊", "快乐加倍~ 🎈"],
            "hide_show": {"hide": "我藏起来啦~ 😜", "show": "我出来啦~ 😝"},
            "angry": ["撞疼我啦！😠", "别再让我撞墙啦！", "哼，我生气了！"],
            "chase": ["我要追上你！🏃", "等等我~ 🤗", "别跑呀~ 😆"],  # 新增：追逐台词
            "being_chased": ["救命呀，有人追我！😱", "别追我啦~ 😟", "我跑不动啦~ 😩"],  # 新增：被追逐台词
            "collision_pet": ["哎呀，撞到你了~ 😳", "对不起呀~ 🥺", "你挡到我啦~ 😝"],  # 新增：宠物间碰撞台词
            "hunger": ["我饿啦~ 🥺", "想吃小鱼干~ 🐟", "给我喂点东西吧~ 😋", "肚子咕咕叫~ 🤤"],  # 新增：饥饿台词
            "menu": {
                # 字典嵌套的嵌套：12个空格（正确：深层嵌套层级）
                "switch_gif": ["换个新造型~", "变变变~", "新衣服好看吗~"],
                "resize": ["尺寸调整完成~", "我变大啦~", "我变小啦~"],
                "alpha": ["透明度调整完成~", "变透明咯~", "又变亮啦~"],
                "auto_move": ["移动状态切换~", "可以自由跑啦~", "乖乖待着不动啦~"],
                "quit": ["再见啦~", "下次再玩~", "拜拜~"],
                "bubble_duration": ["气泡时长设置完成~"],
                "physics": ["物理反馈强度设置完成~"],
                "custom_size": ["宠物尺寸自定义完成~"],
                "custom_alpha": ["透明度自定义完成~"],
                "random": ["随机行为开启啦~ 🎲", "随机行为关闭啦~ 🤐"],
                "chase": ["追逐模式开启啦~ 🏃", "追逐模式关闭啦~ 🛌"]  # 新增：追逐菜单台词
            }
        }
        # ========== 新增：语音控制初始化 ==========\n
        # ========== 语音控制初始化（增加设备检测） ==========
        self.voice_enabled = False  # 语音控制开关
        self.recognizer = sr.Recognizer()  # 语音识别器
        self.microphone = None  # 先初始化为None
        self.has_audio_device = False  # 标记是否有可用输入设备

        # 检测系统是否有可用麦克风
        try:
            mic_list = sr.Microphone.list_microphone_names()
            if len(mic_list) > 0:
                self.has_audio_device = True
                self.microphone = sr.Microphone()  # 有设备才初始化麦克风
            else:
                self.has_audio_device = False
                print("未检测到输入设备，语音控制不可用")
        except Exception as e:
            self.has_audio_device = False
            print(f"检测输入设备失败：{e}，语音控制不可用")

        # 文字转语音引擎（只初始化一次，避免重复占用资源）
        # 百度密钥从 local_secret.py 读取（该文件不提交，见 .gitignore）
        try:
            from local_secret import BAIDU_APP_ID, BAIDU_API_KEY, BAIDU_SECRET_KEY
        except ImportError:
            BAIDU_APP_ID = BAIDU_API_KEY = BAIDU_SECRET_KEY = ""

        if BAIDU_APP_ID and BAIDU_API_KEY and BAIDU_SECRET_KEY:
            self.baidu_client = AipSpeech(BAIDU_APP_ID, BAIDU_API_KEY, BAIDU_SECRET_KEY)
        else:
            # 没有密钥时不创建客户端，语音识别功能整体关闭，避免反复请求报错
            self.baidu_client = None
            print("未配置百度语音密钥，语音识别不可用（请填写 local_secret.py）")
        self.tts_engine = None  # 先初始化标记为None
        try:
            self.tts_engine = pyttsx3.init()
            self.tts_engine.setProperty("rate", 150)  # 语速
            self.tts_engine.setProperty("volume", 1.0)  # 音量（0.0-1.0）
            # 获取系统可用语音列表（用于选择音色）
            self.voice_list = self.tts_engine.getProperty("voices")
            # 切换音色：女性音（索引1，Windows默认）
            if len(self.voice_list) >= 2:
                self.tts_engine.setProperty("voice", self.voice_list[1].id)
                self.show_bubble("语音音色已设置为女性音~ 🎤")  # 调试提示
            else:
                self.tts_engine.setProperty("voice", self.voice_list[0].id)
                self.show_bubble("当前系统仅支持默认音色~ 🎤")  # 调试提示
        except Exception as e:
            self.show_bubble(f"TTS引擎初始化失败：{str(e)} 😟")
            self.tts_engine = None  # 初始化失败则标记为无效

        # 语音指令映射表（语音关键词→对应方法）
        self.voice_commands = {
            # QQ音乐控制
            "播放": self.toggle_qq_music_play,
            "暂停": self.toggle_qq_music_play,
            "上一首": self.qq_music_prev_song,
            "下一首": self.qq_music_next_song,
            # 宠物功能
            "喂食": lambda: self.feed_pet("普通猫粮"),
            "喂小鱼干": lambda: self.feed_pet("美味小鱼干"),
            "开启自动移动": self.enable_auto_move,
            "关闭自动移动": self.disable_auto_move
        }
        # ========== 唤醒词相关配置 ==========\n
        self.wake_word = "小白"  # 自定义唤醒词
        self.in_command_mode = False  # 是否进入指令监听模式（唤醒后激活）
        self.command_timeout = 5  # 指令监听超时时间（秒）
        # ========== 唤醒词参数结束 ==========

        # 顺便启动饥饿值检测（之前遗漏的功能）
        self.check_hunger_status()

        # 气泡窗口（改为主窗口的子窗口）
        self.bubble_window = tk.Toplevel(self.main_root)
        self.bubble_window.overrideredirect(True)
        self.bubble_window.wm_attributes("-topmost", True)
        self.bubble_window.wm_attributes("-alpha", 0.95)
        self.text_label = tk.Label(
            self.bubble_window,
            text="",
            bg="white",
            fg="black",
            font=("微软雅黑", 10, "bold"),
            padx=10,
            pady=6,
            bd=3,
            relief="solid",
            width=20,
            height=2,
            anchor="center"
        )
        self.text_label.pack()
        self.bubble_window.withdraw()

        # 加载配置
        self.load_config()

        # 创建宠物显示标签
        self.label = tk.Label(self.root, image="", bd=0, bg=None)

        # 预加载GIF
        self.preload_all_gifs()
        self.preload_angry_gif()
        self.init_current_gif()

        self.update_gif_display()

        # 绑定事件
        self.root.bind("<ButtonPress-1>", self.on_mouse_down)
        self.root.bind("<B1-Motion>", self.on_mouse_drag)
        self.root.bind("<ButtonRelease-1>", self.on_mouse_up)
        self.root.bind("<Button-3>", self.show_right_menu)
        self.root.bind("<Escape>", lambda e: self.save_and_quit())
        self.root.bind("<Control-a>", lambda e: self.toggle_auto_move())
        self.root.bind("<MouseWheel>", self.on_mouse_wheel)
        self.label.bind("<Button-1>", self.on_click)
        self.label.bind("<Double-1>", self.on_double_click)
        self.root.bind("<Key>", self.on_key_press)

        # 注册实例到全局列表 + 注册GIF哈希到唯一性列表
        PET_INSTANCES.append(self)
        PET_GIF_HASHES.append(self.gif_combination_hash)

        # 启动功能
        self.play_gif_smooth()
        self.auto_move_smooth()
        self.check_attention()
        self.drag_release_bounce_smooth()
        # 新增：启动追逐检测任务
        self.check_chase_target()

    # 补充“上一首”方法
    def qq_music_prev_song(self):
        """控制QQ音乐播放上一首（模拟Ctrl+Left快捷键）"""
        if not self.qq_music_launched:
            self.show_bubble("请先启动QQ音乐~ 😟")
            return
        try:
            self.activate_qq_music_window()
            pyautogui.hotkey("ctrl", "alt", "left")  # QQ音乐“上一首”快捷键
            self.show_bubble("已切换到上一首~ 🎵")
        except Exception as e:
            self.show_bubble(f"上一首切换失败：{str(e)} 😟")

    # 补充“下一首”方法（避免后续同类型错误）
    def qq_music_next_song(self):
        """控制QQ音乐播放下一首（模拟Ctrl+Right快捷键）"""
        if not self.qq_music_launched:
            self.show_bubble("请先启动QQ音乐~ 😟")
            return
        try:
            self.activate_qq_music_window()
            pyautogui.hotkey("ctrl", "alt", "right") # QQ音乐“下一首”快捷键
            self.show_bubble("已切换到下一首~ 🎵")
        except Exception as e:
            self.show_bubble(f"下一首切换失败：{str(e)} 😟")
    def toggle_qq_music_play(self):
        """暂停/播放QQ音乐（模拟空格键，小白也能懂：点一下暂停，再点一下播放）"""
        # 如果QQ音乐还没启动，先提示
        if not self.qq_music_launched:
            self.show_bubble("请先启动QQ音乐~ 😟")
            return
        try:
            # 先激活QQ音乐窗口（不然快捷键没用）
            self.activate_qq_music_window()
            # 模拟按空格键，切换播放/暂停
            pyautogui.hotkey("ctrl", "alt", "f5")
            self.show_bubble("已切换QQ音乐播放状态~ 🎶")
        except Exception as e:
            # 出错了就提示失败原因
            self.show_bubble(f"播放控制失败：{str(e)} 😟")

    def activate_qq_music_window(self):
        """激活QQ音乐窗口（大白话：把QQ音乐窗口调到最前面，确保快捷键生效）"""
        try:
            # 找到标题带“QQ音乐”的窗口
            qq_music_windows = gw.getWindowsWithTitle("QQ音乐")
            if qq_music_windows:
                # 把第一个QQ音乐窗口调到最前面
                qq_music_windows[0].activate()
                time.sleep(0.5)  # 等0.5秒，确保窗口激活
        except:
            # 找不到窗口也不报错，默默跳过
            pass

    def auto_play_qq_music(self):
        """启动QQ音乐（仅启动，不自动播放）"""
        # 已启动则直接返回，不重复启动
        if self.qq_music_launched:
            self.show_bubble("QQ音乐已启动~ 😎")
            return

        # QQ音乐的默认安装路径（32位和64位都包含）
        qq_music_paths = {
            "Windows": [
                r"C:\Program Files (x86)\Tencent\QQMusic\QQMusic.exe",
                r"C:\Program Files\Tencent\QQMusic\QQMusic.exe"
            ]
        }

        # 获取系统类型（这里只支持Windows）
        sys_type = platform.system()
        qq_music_path = None
        if sys_type in qq_music_paths:
            # 遍历路径，找到存在的那个
            for path in qq_music_paths[sys_type]:
                if os.path.exists(path):
                    qq_music_path = path
                    break

        if qq_music_path:
            try:
                # 启动QQ音乐
                os.startfile(qq_music_path)
                time.sleep(2)  # 等2秒，让QQ音乐完全启动
                # 不是生气状态就提示启动成功
                if not self.is_angry and not self.angry_dialog_shown:
                    self.show_bubble("QQ音乐启动成功~ 🎵")
                self.qq_music_launched = True  # 标记为已启动
            except Exception as e:
                self.show_bubble(f"QQ音乐启动失败：{str(e)} 😟")
        else:
            self.show_bubble("未找到QQ音乐安装路径~ 😥")

    # ========== 新增：语音控制核心方法 ==========
    def toggle_voice_control(self):
        """切换语音控制开关（右键菜单中调用）"""
        # 无输入设备时直接提示
        if not self.has_audio_device:
            self.show_bubble("未检测到输入设备（麦克风），暂时无法使用语音控制~ 😟")
            return

        # 未配置百度语音密钥时直接提示（密钥写在 local_secret.py）
        if not self.baidu_client:
            self.show_bubble("未配置百度语音密钥，语音控制不可用~ 请填写 local_secret.py 😟")
            return

        self.voice_enabled = not self.voice_enabled
        if self.voice_enabled:
            # 先判断TTS引擎是否有效
            if not self.tts_engine:
                self.show_bubble("TTS语音引擎未初始化，无法使用语音回复功能~ 😟")
            self.show_bubble("语音控制已开启，可说出指令（如“播放音乐”）~ 🎤")
            # 启动语音识别线程（daemon=True：主线程退出时，子线程自动退出）
            threading.Thread(target=self.voice_recognition_loop, daemon=True).start()
        else:
            self.show_bubble("语音控制已关闭~ 🎤")

    def voice_recognition_loop(self):
        """语音识别主循环：修复麦克风占用，适配百度官方SDK"""
        # 无麦克风或未配置密钥时直接退出，避免空转报错
        if not self.microphone or not self.baidu_client:
            return
        # 麦克风只占用一次，解决"source is already inside"错误
        with self.microphone as source:
            self.recognizer.adjust_for_ambient_noise(source)  # 仅一次降噪
            print("语音监听已启动，等待唤醒词「小白」...")
            while self.voice_enabled and self.is_alive:
                try:
                    if not self.in_command_mode:
                        # 1. 唤醒词监听模式（监听2秒，无超时）
                        audio = self.recognizer.listen(source, phrase_time_limit=2)
                        # 关键替换：将音频转为百度要求的格式（16k采样率wav）
                        audio_data = audio.get_wav_data(convert_rate=16000)
                        # 调用百度SDK识别（替换原来的recognize_baidu）
                        result = self.baidu_client.asr(
                            audio_data,
                            "wav",
                            16000,
                            {"dev_pid": 1537}  # 1537=中文普通话，固定值
                        )
                        # 处理识别结果
                        if result["err_no"] == 0:
                            text = result["result"][0].strip()  # 获取识别文字
                            print(f"识别到语音：{text}")
                            # 匹配唤醒词
                            if self.wake_word in text:
                                self.in_command_mode = True
                                tip_text = f"我在呢~ 请说出指令（{self.command_timeout}秒内有效）"
                                self.show_bubble(tip_text)
                                # 语音回复
                                if self.tts_engine:
                                    self.tts_engine.say("我在呢，请说出指令")
                                    self.tts_engine.runAndWait()
                        else:
                            # 识别失败不弹窗，只打印日志
                            print(f"唤醒词识别失败：{result['err_msg']}")
                            continue
                    else:
                        # 2. 指令监听模式（唤醒后激活，超时5秒）
                        audio = self.recognizer.listen(
                            source,
                            timeout=self.command_timeout,
                            phrase_time_limit=3
                        )
                        # 同样替换为百度SDK识别
                        audio_data = audio.get_wav_data(convert_rate=16000)
                        result = self.baidu_client.asr(
                            audio_data,
                            "wav",
                            16000,
                            {"dev_pid": 1537}
                        )
                        # 处理指令结果
                        if result["err_no"] == 0:
                            text = result["result"][0].strip()
                            print(f"识别到指令：{text}")
                            self.show_bubble(f"识别到指令：{text}~")
                            self.match_voice_command(text)
                            self.in_command_mode = False  # 执行完返回唤醒模式
                        else:
                            print(f"指令识别失败：{result['err_msg']}")
                            self.in_command_mode = False
                # 下面的异常处理和你原来的一致，无需修改
                except sr.WaitTimeoutError:
                    if self.in_command_mode:
                        timeout_tip = f"{self.command_timeout}秒未收到指令，等待再次唤醒~ 😴"
                        self.show_bubble(timeout_tip)
                        self.in_command_mode = False
                except sr.UnknownValueError:
                    if self.in_command_mode:
                        self.show_bubble("没听清指令哦~ 😟")
                        self.in_command_mode = False
                except Exception as e:
                    unknown_error_tip = f"语音控制出错：{str(e)} 😟"
                    print(f"语音线程异常：{unknown_error_tip}")
                    self.show_bubble(unknown_error_tip)
                    self.in_command_mode = False
                time.sleep(0.2)  # 降低CPU占用

    def match_voice_command(self, text):
        #\"\"\"匹配语音指令并执行对应功能\"\"\"\
        # 按关键词长度降序排序，优先匹配长关键词，避免匹配冲突
        sorted_commands = sorted(self.voice_commands.items(), key=lambda x: len(x[0]), reverse=True)
        for keyword, func in sorted_commands:
            if keyword in text:
                print(f"成功匹配指令：{keyword}")  # 调试打印，确认匹配结果
                func()  # 执行对应方法
                # 语音回复执行结果（先判断TTS引擎是否有效）
                if self.tts_engine:
                    self.tts_engine.say(f"已为你{keyword}")
                    self.tts_engine.runAndWait()
                return
        print(f"未匹配到指令：{text}")  # 调试打印，确认未匹配的内容
        self.show_bubble(f"暂时不支持“{text}”这个指令哦~ 😟")
    # ========== 语音控制方法结束 ==========

    def check_hunger_status(self):
        """定期检测饥饿值，自动下降并触发饥饿提示"""
        # 窗口无效或实例死亡则停止检测
        if not self.root.winfo_exists() or not self.is_alive:
            return

        # 饥饿值自动下降（上限100，下限0）
        current_time = time.time()
        if current_time - self.last_operate_time > 1:  # 每1秒更新一次
            self.hunger_value = max(0, min(100, self.hunger_value - self.hunger_down_speed / 10))
            self.last_operate_time = current_time  # 避免与注意力检测冲突

        # 饥饿值低于20时，显示饥饿提示
        if self.hunger_value < 20 and not self.is_angry and not self.angry_dialog_shown and not self.is_bubble_showing:
            hunger_dialog = random.choice(["我饿啦~ 🥺", "想吃小鱼干~ 🐟", "给我喂点东西吧~ 😋"])
            self.show_bubble(hunger_dialog)

        # 递归启动定时器（每1000ms检测一次）
        self.hunger_check_task = self.root.after(1000, self.check_hunger_status)

    # ========== 新增：喂食核心逻辑 ==========
    def feed_pet(self, food_name):
        """
        给宠物喂食
        :param food_name: 食物名称（对应self.feed_items中的key）
        """
        # 校验喂食条件
        current_time = time.time()
        if (current_time - self.last_feed_time < self.feed_cooldown) or self.is_feeding:
            return

        # 获取食物恢复的饥饿值
        restore_value = self.feed_items.get(food_name, 0)
        if restore_value <= 0:
            return

        # 更新喂食状态与饥饿值
        self.is_feeding = True
        self.last_feed_time = current_time
        self.hunger_value = max(0, min(100, self.hunger_value + restore_value))

        # 显示喂食成功提示
        feed_dialog = random.choice([
            f"真好吃！谢谢主人的{food_name}~ 😋",
            f"{food_name}太美味啦！饱腹值+{restore_value} 🥰",
            f"嗝~ 吃饱啦，饥饿值现在是{int(self.hunger_value)}~ 😌"
        ])
        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(feed_dialog)

        # 重置喂食状态（冷却时间后）
        def reset_feeding_status():
            self.is_feeding = False

        self.root.after(int(self.feed_cooldown * 1000), reset_feeding_status)


    # ========== 新增：计算GIF组合哈希值（用于唯一性校验） ==========
    def calc_gif_combination_hash(self, gif_list, angry_gif):
        """将GIF路径组合转换为唯一哈希值，用于判断宠物是否重复"""
        combined_str = "|".join(gif_list) + "|" + angry_gif
        return hash(combined_str)

    # ========== 新增：追逐目标检测与切换 ==========
    def check_chase_target(self):
        """检测是否有可追逐的宠物，并切换追逐状态"""
        # 窗口不存在或实例无效则停止检测
        if not self.root.winfo_exists() or not self.is_alive or not self.is_auto_move:
            self.main_root.after(1000, self.check_chase_target)
            return

        # 追逐冷却时间未到，不切换目标
        current_time = time.time()
        if current_time - self.last_chase_switch_time < self.chase_cool_down / 1000:
            self.main_root.after(1000, self.check_chase_target)
            return

        # 筛选有效目标（排除自身、已失效实例）
        valid_targets = [
            pet for pet in PET_INSTANCES
            if pet is not self and pet.is_alive and pet.root.winfo_exists()
        ]

        if not valid_targets:
            # 无有效目标，取消追逐
            self.is_chasing = False
            self.is_being_chased = False
            self.target_pet = None
            # 恢复基础移动速度
            self.move_speed_x = self.base_move_speed_x
            self.move_speed_y = self.base_move_speed_y
            self.main_root.after(1000, self.check_chase_target)
            return

        # 计算与每个有效目标的距离
        self_x = self.root.winfo_x() + self.pet_width / 2
        self_y = self.root.winfo_y() + self.pet_height / 2
        target_distances = []

        for target in valid_targets:
            target_x = target.root.winfo_x() + target.pet_width / 2
            target_y = target.root.winfo_y() + target.pet_height / 2
            # 欧几里得距离
            distance = ((self_x - target_x) ** 2 + (self_y - target_y) ** 2) ** 0.5
            target_distances.append((target, distance))

        # 按距离排序，取最近的目标
        target_distances.sort(key=lambda x: x[1])
        closest_target, closest_distance = target_distances[0]

        # 判断是否触发追逐（距离小于阈值）
        if closest_distance < self.chase_distance_threshold and not self.is_chasing:
            # 开启追逐状态
            self.is_chasing = True
            self.target_pet = closest_target
            self.target_pet.is_being_chased = True
            self.last_chase_switch_time = current_time
            # 放大移动速度（追逐倍率）
            self.adjust_chase_speed()
            # 显示追逐台词
            if not self.is_angry and not self.angry_dialog_shown:
                self.show_bubble(self.generate_random_dialogue("chase"))
        elif closest_distance >= self.chase_distance_threshold and self.is_chasing:
            # 超出距离阈值，取消追逐
            self.is_chasing = False
            if self.target_pet:
                self.target_pet.is_being_chased = False
            self.target_pet = None
            self.last_chase_switch_time = current_time
            # 恢复基础移动速度
            self.move_speed_x = self.base_move_speed_x
            self.move_speed_y = self.base_move_speed_y
            # 显示被追逐结束台词（仅被追逐方）
            if self.is_being_chased:
                self.is_being_chased = False
                if not self.is_angry and not self.angry_dialog_shown:
                    self.show_bubble("终于摆脱啦~ 😌")

        # 递归检测
        self.main_root.after(1000, self.check_chase_target)

    # ========== 新增：调整追逐速度（朝向目标移动） ==========
    def adjust_chase_speed(self):
        """调整移动速度，朝向追逐目标移动"""
        if not self.is_chasing or not self.target_pet or not self.target_pet.root.winfo_exists():
            return

        # 计算自身与目标的中心坐标
        self_x = self.root.winfo_x() + self.pet_width / 2
        self_y = self.root.winfo_y() + self.pet_height / 2
        target_x = self.target_pet.root.winfo_x() + self.target_pet.pet_width / 2
        target_y = self.target_pet.root.winfo_y() + self.target_pet.pet_height / 2

        # 计算方向向量
        dx = target_x - self_x
        dy = target_y - self_y
        # 归一化方向向量（确保速度方向正确）
        distance = ((dx ** 2) + (dy ** 2)) ** 0.5
        if distance == 0:
            return

        dx_normalized = dx / distance
        dy_normalized = dy / distance

        # 基于基础速度 + 追逐倍率，设置朝向目标的移动速度
        self.move_speed_x = dx_normalized * abs(self.base_move_speed_x) * self.chase_speed_multiplier
        self.move_speed_y = dy_normalized * abs(self.base_move_speed_y) * self.chase_speed_multiplier

    # ========== 新增：切换追逐模式（开启/关闭） ==========
    def toggle_chase_mode(self):
        """手动切换追逐模式（全局开启/关闭）"""
        if self.is_chasing:
            # 关闭追逐
            self.is_chasing = False
            if self.target_pet:
                self.target_pet.is_being_chased = False
            self.target_pet = None
            # 恢复基础速度
            self.move_speed_x = self.base_move_speed_x
            self.move_speed_y = self.base_move_speed_y
            dialog = self.generate_random_dialogue("chase")
        else:
            # 开启追逐（立即检测目标）
            self.last_chase_switch_time = 0  # 重置冷却时间
            self.check_chase_target()
            dialog = self.generate_random_dialogue("chase")

        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(dialog)

    # ========== 强化：宠物间碰撞逻辑（新增碰撞台词+更强反弹） ==========
    def check_pet_collision(self, win_x, win_y, win_width, win_height):
        """强化宠物间碰撞检测，返回碰撞后的位置和状态"""
        collided = False
        collision_target = None

        for other_pet in PET_INSTANCES:
            if (other_pet is self) or (not other_pet.is_alive) or (not other_pet.root.winfo_exists()):
                continue

            # 获取其他宠物的位置和尺寸
            other_win_x = other_pet.root.winfo_x()
            other_win_y = other_pet.root.winfo_y()
            other_win_width = other_pet.root.winfo_width()
            other_win_height = other_pet.root.winfo_height()

            # 矩形重叠判定：强化碰撞检测（包含边界缓冲）
            is_collided = (
                win_x - 5 < other_win_x + other_win_width and
                win_x + win_width + 5 > other_win_x and
                win_y - 5 < other_win_y + other_win_height and
                win_y + win_height + 5 > other_win_y
            )

            if is_collided:
                collided = True
                collision_target = other_pet
                # 强化反弹：互相反向且放大反弹力度（反弹系数*1.2）
                temp_speed_x = self.move_speed_x
                temp_speed_y = self.move_speed_y

                self.move_speed_x = -other_pet.move_speed_x * self.bounce_coeff * 1.2
                self.move_speed_y = -other_pet.move_speed_y * self.bounce_coeff * 1.2
                other_pet.move_speed_x = -temp_speed_x * other_pet.bounce_coeff * 1.2
                other_pet.move_speed_y = -temp_speed_y * other_pet.bounce_coeff * 1.2

                # 位置偏移：避免重叠卡死（偏移量放大）
                win_x += self.move_speed_x * 5
                win_y += self.move_speed_y * 5

                # 边界二次校正
                win_x = max(20, min(win_x, self.screen_width - win_width - 20))
                win_y = max(20, min(win_y, self.screen_height - win_height - 20))

                # 触发生气状态（可选）
                if not self.is_angry and not self.angry_dialog_shown:
                    self.switch_to_angry("collision")
                    # 显示宠物间碰撞台词
                    self.show_bubble(self.generate_random_dialogue("collision_pet"))
                    # 对方宠物也显示碰撞台词
                    if not other_pet.is_angry and not other_pet.angry_dialog_shown:
                        other_pet.show_bubble(other_pet.generate_random_dialogue("collision_pet"))

                break  # 避免同时与多个宠物碰撞导致速度异常

        return win_x, win_y, collided, collision_target

    def preload_all_gifs(self):
        print("开始预加载普通GIF...")
        if self.pet_width <= 0 or self.pet_height <= 0:
            print(f"警告：宠物尺寸无效，已自动修正")
            self.pet_width = 150
            self.pet_height = 180
        target_size = (self.pet_width, self.pet_height)
        for idx, gif_path in enumerate(self.gif_path_list):
            temp_frames = []
            temp_delays = []
            try:
                if not os.path.exists(gif_path):
                    print(f"跳过不存在的文件：{gif_path}")
                    continue
                gif = Image.open(gif_path)
                while True:
                    gif_resized = gif.resize(target_size, Image.Resampling.LANCZOS)
                    # 绑定图片到当前宠物窗口，避免资源冲突
                    frame = ImageTk.PhotoImage(gif_resized.copy(), master=self.root)
                    temp_frames.append(frame)
                    frame_delay = gif.info.get("duration", 100)
                    temp_delays.append(max(frame_delay, self.min_frame_delay))
                    gif.seek(gif.tell() + 1)
            except EOFError:
                self.preloaded_frames[f"normal_{idx}"] = (temp_frames, temp_delays)
            except Exception as e:
                print(f"预加载{gif_path}失败：{e}")
        print("普通GIF预加载完成！")

    def preload_angry_gif(self):
        print(f"开始预加载生气GIF：{self.angry_gif_path}")
        if self.pet_width <= 0 or self.pet_height <= 0:
            print(f"警告：宠物尺寸无效，已自动修正")
            self.pet_width = 150
            self.pet_height = 180
        target_size = (self.pet_width, self.pet_height)
        temp_frames = []
        temp_delays = []
        try:
            if not os.path.exists(self.angry_gif_path):
                print(f"生气GIF不存在：{self.angry_gif_path}")
                return
            gif = Image.open(self.angry_gif_path)
            while True:
                gif_resized = gif.resize(target_size, Image.Resampling.LANCZOS)
                # 绑定图片到当前宠物窗口，避免资源冲突
                frame = ImageTk.PhotoImage(gif_resized.copy(), master=self.root)
                temp_frames.append(frame)
                frame_delay = gif.info.get("duration", 100)
                temp_delays.append(max(frame_delay, self.min_frame_delay))
                gif.seek(gif.tell() + 1)
        except EOFError:
            self.preloaded_frames["angry"] = (temp_frames, temp_delays)
        except Exception as e:
            print(f"预加载生气GIF失败：{e}")
        print("生气GIF预加载完成！")

    def init_current_gif(self):
        self.gif_frames = []
        self.frame_delays = []
        if self.preloaded_frames:
            first_normal_key = next((k for k in self.preloaded_frames if k.startswith("normal_")), None)
            if first_normal_key:
                self.gif_frames, self.frame_delays = self.preloaded_frames[first_normal_key]
        else:
            print("警告：无有效GIF文件，宠物显示异常！")

    def update_gif_display(self):
        if self.gif_frames:
            self.label.config(image=self.gif_frames[0])
            self.current_frame_idx = 0
        self.label.pack()

    def generate_random_dialogue(self, scene_type):
        if scene_type == "angry":
            return random.choice(self.dialogue_lib["angry"])
        elif scene_type == "click":
            return random.choice(self.dialogue_lib["click"])
        elif scene_type == "double_click":
            return random.choice(self.dialogue_lib["double_click"])
        elif scene_type == "attention":
            return random.choice(self.dialogue_lib["attention"])
        elif scene_type == "space":
            return random.choice(self.dialogue_lib["space"])
        elif scene_type == "hide":
            return self.dialogue_lib["hide_show"]["hide"]
        elif scene_type == "show":
            return self.dialogue_lib["hide_show"]["show"]
        elif scene_type == "chase":
            return random.choice(self.dialogue_lib["chase"])
        elif scene_type == "being_chased":
            return random.choice(self.dialogue_lib["being_chased"])
        elif scene_type == "collision_pet":
            return random.choice(self.dialogue_lib["collision_pet"])
        elif scene_type == "hunger":  # 新增：饥饿场景台词
            return random.choice(self.dialogue_lib["hunger"])
        elif scene_type == "random":
            return random.choice(self.dialogue_lib["menu"]["random"])
        elif scene_type in self.dialogue_lib["menu"].keys():
            return random.choice(self.dialogue_lib["menu"][scene_type])
        else:
            return random.choice(["嘿嘿~", "主人好~", "真好玩~"])

    def play_gif_smooth(self):
        if self.gif_animation_task is not None:
            try:
                self.root.after_cancel(self.gif_animation_task)
            except:
                pass

        if not self.root.winfo_exists():
            return

        if self.is_angry:
            frames, delays = self.preloaded_frames.get("angry", ([], []))
        else:
            frames, delays = self.gif_frames, self.frame_delays

        if not frames or not self.is_gif_playing:
            self.gif_animation_task = self.root.after(self.min_frame_delay, self.play_gif_smooth)
            return

        self.label.config(image=frames[self.current_frame_idx])
        self.current_frame_idx = (self.current_frame_idx + 1) % len(frames)
        current_delay = delays[self.current_frame_idx] if delays else self.min_frame_delay

        self.gif_animation_task = self.root.after(int(current_delay), self.play_gif_smooth)

    # ========== 强化：自动移动（整合追逐逻辑+强化碰撞） ==========
    def auto_move_smooth(self):
        if self.move_task is not None:
            try:
                self.root.after_cancel(self.move_task)
            except:
                pass

        if not self.root.winfo_exists() or not self.is_alive:
            return

        if self.is_auto_move and not self.is_dragging:
            win_x = self.root.winfo_x()
            win_y = self.root.winfo_y()
            win_width = self.root.winfo_width()
            win_height = self.root.winfo_height()

            # 新增：追逐状态下，实时调整朝向目标的速度
            if self.is_chasing and self.target_pet and self.target_pet.root.winfo_exists():
                self.adjust_chase_speed()

            # 屏幕边界碰撞检测与反弹
            if win_x <= 20 or win_x + win_width >= self.screen_width - 20:
                self.move_speed_x = -self.move_speed_x * self.bounce_coeff
                win_x = max(20, min(win_x, self.screen_width - win_width - 20))
            if win_y <= 20 or win_y + win_height >= self.screen_height - 20:
                self.move_speed_y = -self.move_speed_y * self.bounce_coeff
                win_y = max(20, min(win_y, self.screen_height - win_height - 20))

            # 强化：宠物间碰撞检测
            win_x, win_y, collided, _ = self.check_pet_collision(win_x, win_y, win_width, win_height)

            # 更新位置
            new_x = win_x + self.move_speed_x
            new_y = win_y + self.move_speed_y
            new_x = max(20, min(new_x, self.screen_width - win_width - 20))
            new_y = max(20, min(new_y, self.screen_height - win_height - 20))
            self.root.geometry(f"+{int(new_x)}+{int(new_y)}")
            self.update_bubble_position()

        self.move_task = self.root.after(5, self.auto_move_smooth)

    def switch_to_angry(self, source):
        if source not in ["drag", "collision"] or "angry" not in self.preloaded_frames or self.angry_dialog_shown:
            return

        self.is_angry = True
        self.angry_dialog_shown = True
        self.current_frame_idx = 0
        self.gif_frames, self.frame_delays = self.preloaded_frames.get("angry", ([], []))
        self.update_gif_display()

        dialog = self.generate_random_dialogue("angry")
        self.show_bubble(dialog, force_show=True)

        def reset_angry_state():
            self.is_angry = False
            self.current_frame_idx = 0
            self.init_current_gif()
            self.update_gif_display()

            def reset_dialog_flag():
                self.angry_dialog_shown = False

            self.main_root.after(self.angry_dialog_cooldown, reset_dialog_flag)

        self.main_root.after(self.angry_duration, reset_angry_state)

    def update_bubble_position(self):
        try:
            if not hasattr(self, 'bubble_window') or not hasattr(self, 'text_label'):
                return
            pet_x = self.root.winfo_x()
            pet_y = self.root.winfo_y()
            pet_width = self.root.winfo_width()
            pet_height = self.root.winfo_height()
            bubble_width = self.text_label.winfo_width()
            bubble_height = self.text_label.winfo_height()

            bubble_x = pet_x + pet_width + 5
            bubble_y = pet_y + (pet_height - bubble_height) // 2

            if bubble_x + bubble_width > self.screen_width - 20:
                bubble_x = pet_x - bubble_width - 5
            if bubble_y < 20:
                bubble_y = 20
            if bubble_y + bubble_height > self.screen_height - 20:
                bubble_y = self.screen_height - bubble_height - 20

            self.bubble_window.geometry(f"+{int(bubble_x)}+{int(bubble_y)}")
        except Exception as e:
            pass

    def show_bubble(self, text, force_show=False):
        if not hasattr(self, 'bubble_window') or not hasattr(self, 'text_label') or not hasattr(self, 'root'):
            print("警告：气泡依赖组件未初始化，无法显示对话")
            return

        if not self.root.winfo_exists() or not self.bubble_window.winfo_exists():
            return

        if self.bubble_hide_task is not None:
            try:
                self.main_root.after_cancel(self.bubble_hide_task)
            except:
                pass

        self.text_label.config(text=text)
        self.text_label.update_idletasks()
        self.update_bubble_position()

        self.bubble_window.deiconify()
        self.is_bubble_showing = True

        self.bubble_window.update_idletasks()
        self.root.update_idletasks()

        def hide_bubble():
            if self.root.winfo_exists() and self.bubble_window.winfo_exists():
                self.bubble_window.withdraw()
                self.text_label.config(text="")
                self.is_bubble_showing = False

        self.bubble_hide_task = self.main_root.after(self.bubble_duration, hide_bubble)

    def set_bubble_duration_1s(self):
        self.bubble_duration = 1000
        self.show_bubble(self.generate_random_dialogue("bubble_duration") + "（1秒）")

    def set_bubble_duration_3s(self):
        self.bubble_duration = 3000
        self.show_bubble(self.generate_random_dialogue("bubble_duration") + "（3秒）")

    def set_bubble_duration_5s(self):
        self.bubble_duration = 5000
        self.show_bubble(self.generate_random_dialogue("bubble_duration") + "（5秒）")

    def set_bubble_duration_10s(self):
        self.bubble_duration = 10000
        self.show_bubble(self.generate_random_dialogue("bubble_duration") + "（10秒）")

    def set_bubble_duration_custom(self):
        custom_window = tk.Toplevel(self.main_root)
        custom_window.title("自定义气泡时长")
        custom_window.geometry("250x100")
        custom_window.wm_attributes("-topmost", True)

        tk.Label(custom_window, text="请输入气泡时长（单位：秒）：").pack(pady=10)
        duration_entry = tk.Entry(custom_window, width=10)
        duration_entry.pack()
        duration_entry.insert(0, str(self.bubble_duration / 1000))

        def confirm_custom():
            try:
                input_seconds = float(duration_entry.get())
                if input_seconds <= 0:
                    self.show_bubble("时长不能为负数~")
                else:
                    self.bubble_duration = int(input_seconds * 1000)
                    self.show_bubble(f"气泡时长已设为{input_seconds}秒~")
                custom_window.destroy()
            except ValueError:
                self.show_bubble("请输入有效数字~")
                custom_window.destroy()

        tk.Button(custom_window, text="确认", command=confirm_custom).pack(pady=5)

    def on_mouse_down(self, event):
        self.is_dragging = False
        self.start_x_root = event.x_root
        self.start_y_root = event.y_root
        self.win_start_x = self.root.winfo_x()
        self.win_start_y = self.root.winfo_y()
        self.start_x = event.x
        self.start_y = event.y
        self.last_operate_time = time.time()
        self.drag_release_speed_x = 0
        self.drag_release_speed_y = 0

    def on_mouse_drag(self, event):
        self.move_offset_x = abs(event.x - self.start_x)
        self.move_offset_y = abs(event.y - self.start_y)
        if self.move_offset_x > self.drag_threshold or self.move_offset_y > self.drag_threshold:
            self.is_dragging = True
            if self.is_gif_playing:
                self.is_gif_playing = False

            mouse_move_x = event.x_root - self.start_x_root
            mouse_move_y = event.y_root - self.start_y_root

            self.drag_release_speed_x = mouse_move_x * self.inertia_coeff
            self.drag_release_speed_y = mouse_move_y * self.inertia_coeff

            new_x = self.win_start_x + mouse_move_x
            new_y = self.win_start_y + mouse_move_y
            new_x = max(20, min(new_x, self.screen_width - self.root.winfo_width() - 20))
            new_y = max(20, min(new_y, self.screen_height - self.root.winfo_height() - 20))
            self.root.geometry(f"+{int(new_x)}+{int(new_y)}")

            self.start_x_root = event.x_root
            self.win_start_x = new_x
            self.start_y_root = event.y_root
            self.win_start_y = new_y
            self.start_x = event.x
            self.start_y = event.y

            self.update_bubble_position()
        self.last_operate_time = time.time()

    def on_mouse_up(self, event):
        if not self.is_gif_playing:
            self.is_gif_playing = True
            self.play_gif_smooth()
        self.is_dragging = False
        self.last_operate_time = time.time()
        self.drag_release_bounce_smooth()

    def drag_release_bounce_smooth(self):
        if self.bounce_task is not None:
            try:
                self.root.after_cancel(self.bounce_task)
            except:
                pass

        if self.is_dragging or not self.root.winfo_exists() or not self.is_alive:
            return

        speed_threshold = 0.5
        if abs(self.drag_release_speed_x) < speed_threshold and abs(self.drag_release_speed_y) < speed_threshold:
            self.drag_release_speed_x = 0
            self.drag_release_speed_y = 0
            return

        win_x = self.root.winfo_x()
        win_y = self.root.winfo_y()
        win_width = self.root.winfo_width()
        win_height = self.root.winfo_height()

        new_x = win_x + self.drag_release_speed_x
        new_y = win_y + self.drag_release_speed_y
        collided = False
        x_bounce = False
        y_bounce = False

        if new_x <= 20:
            new_x = 20
            self.drag_release_speed_x = -self.drag_release_speed_x * self.bounce_coeff
            x_bounce = True
            collided = True
        elif new_x + win_width >= self.screen_width - 20:
            new_x = self.screen_width - win_width - 20
            self.drag_release_speed_x = -self.drag_release_speed_x * self.bounce_coeff
            x_bounce = True
            collided = True

        if new_y <= 20:
            new_y = 20
            self.drag_release_speed_y = -self.drag_release_speed_y * self.bounce_coeff
            y_bounce = True
            collided = True
        elif new_y + win_height >= self.screen_height - 20:
            new_y = self.screen_height - win_height - 20
            self.drag_release_speed_y = -self.drag_release_speed_y * self.bounce_coeff
            y_bounce = True
            collided = True

        if collided and not self.is_angry and not self.angry_dialog_shown:
            self.switch_to_angry("drag")

        self.root.geometry(f"+{int(new_x)}+{int(new_y)}")

        if not x_bounce:
            self.drag_release_speed_x *= self.damping_coeff
        if not y_bounce:
            self.drag_release_speed_y *= self.damping_coeff

        self.update_bubble_position()
        self.bounce_task = self.root.after(5, self.drag_release_bounce_smooth)

    def set_physics_coeff(self, inertia=None, damping=None, bounce=None):
        if inertia is not None:
            self.inertia_coeff = max(0.1, min(inertia, 2.0))
        if damping is not None:
            self.damping_coeff = max(0.8, min(damping, 0.99))
        if bounce is not None:
            self.bounce_coeff = max(0.1, min(bounce, 1.5))
        self.show_bubble(self.generate_random_dialogue("physics"))

    def set_physics_custom(self):
        custom_window = tk.Toplevel(self.main_root)
        custom_window.title("自定义物理反馈强度")
        custom_window.geometry("300x180")
        custom_window.wm_attributes("-topmost", True)

        tk.Label(custom_window, text="惯性强度（0.1-2.0，默认0.8）：").pack(pady=5)
        inertia_entry = tk.Entry(custom_window, width=10)
        inertia_entry.pack()
        inertia_entry.insert(0, str(self.inertia_coeff))

        tk.Label(custom_window, text="阻尼强度（0.8-0.99，默认0.95）：").pack(pady=5)
        damping_entry = tk.Entry(custom_window, width=10)
        damping_entry.pack()
        damping_entry.insert(0, str(self.damping_coeff))

        tk.Label(custom_window, text="反弹强度（0.1-1.5，默认0.8）：").pack(pady=5)
        bounce_entry = tk.Entry(custom_window, width=10)
        bounce_entry.pack()
        bounce_entry.insert(0, str(self.bounce_coeff))

        def confirm_custom():
            try:
                inertia = float(inertia_entry.get())
                damping = float(damping_entry.get())
                bounce = float(bounce_entry.get())
                self.set_physics_coeff(inertia, damping, bounce)
                custom_window.destroy()
            except ValueError:
                self.show_bubble("请输入有效数字~")
                custom_window.destroy()

        tk.Button(custom_window, text="确认", command=confirm_custom).pack(pady=10)

    def on_mouse_wheel(self, event):
        delta = event.delta
        if delta > 0:
            self.pet_width = min(int(self.pet_width * 1.1), 400)
            self.pet_height = min(int(self.pet_height * 1.1), 400)
        else:
            self.pet_width = max(int(self.pet_width * 0.9), 50)
            self.pet_height = max(int(self.pet_height * 0.9), 60)
        self.preload_all_gifs()
        self.preload_angry_gif()
        self.init_current_gif()
        self.update_gif_display()
        dialog = self.generate_random_dialogue("resize")
        self.show_bubble(dialog)
        self.update_bubble_position()
        self.last_operate_time = time.time()

    def on_click(self, event):
        self.last_operate_time = time.time()
        dialog = self.generate_random_dialogue("click")
        self.show_bubble(dialog)

    def on_double_click(self, event):
        self.last_operate_time = time.time()
        old_width = self.pet_width
        old_height = self.pet_height

        self.pet_width = int(old_width * 1.3)
        self.pet_height = int(old_height * 1.3)
        self.preload_all_gifs()
        self.preload_angry_gif()
        self.init_current_gif()
        self.update_gif_display()

        self.root.wm_attributes("-alpha", 0.6)
        self.root.after(200, lambda: self.root.wm_attributes("-alpha", 1.0))
        self.root.after(400, lambda: self.root.wm_attributes("-alpha", 0.6))
        self.root.after(600, lambda: self.root.wm_attributes("-alpha", 1.0))

        self.root.after(800, lambda: self.restore_pet_size(old_width, old_height))

        dialog = self.generate_random_dialogue("double_click")
        self.show_bubble(dialog)

    def on_key_press(self, event):
        self.last_operate_time = time.time()
        if event.keysym == "space":
            old_width = self.pet_width
            old_height = self.pet_height
            self.pet_width = int(old_width * 1.2)
            self.pet_height = int(old_height * 1.2)
            self.preload_all_gifs()
            self.preload_angry_gif()
            self.init_current_gif()
            self.update_gif_display()
            self.root.after(500, lambda: self.restore_pet_size(old_width, old_height))

            dialog = self.generate_random_dialogue("space")
            self.show_bubble(dialog)

        if event.keysym == "d" and (event.state & 0x4):
            self.is_hide_mode = not self.is_hide_mode
            if self.is_hide_mode:
                self.root.wm_attributes("-alpha", 0.5)
                dialog = self.generate_random_dialogue("hide")
            else:
                self.root.wm_attributes("-alpha", 1.0)
                dialog = self.generate_random_dialogue("show")
            self.show_bubble(dialog)

    def check_attention(self):
        if not self.root.winfo_exists() or not self.is_alive:
            return
        current_time = time.time()
        if current_time - self.last_operate_time > self.attention_wait_time and not self.is_dragging:
            self.init_current_gif()
            self.update_gif_display()

            win_x = self.root.winfo_x()
            win_y = self.root.winfo_y()
            self.root.geometry(f"+{int(win_x + 5)}+{int(win_y)}")
            self.root.after(100, lambda: self.root.geometry(f"+{int(win_x - 5)}+{int(win_y)}"))
            self.root.after(200, lambda: self.root.geometry(f"+{int(win_x + 5)}+{int(win_y)}"))
            self.root.after(300, lambda: self.root.geometry(f"+{int(win_x - 5)}+{int(win_y)}"))
            self.root.after(400, lambda: self.root.geometry(f"+{int(win_x)}+{int(win_y)}"))

            dialog = self.generate_random_dialogue("attention")
            if not self.is_angry and not self.angry_dialog_shown:
                self.show_bubble(dialog)

        self.main_root.after(1000, self.check_attention)

    def restore_pet_size(self, old_width, old_height):
        self.pet_width = old_width
        self.pet_height = old_height
        self.preload_all_gifs()
        self.preload_angry_gif()
        self.init_current_gif()
        self.update_gif_display()

    def toggle_auto_move(self):
        self.is_auto_move = not self.is_auto_move
        # 关闭自动移动时，同时关闭追逐模式
        if not self.is_auto_move:
            self.is_chasing = False
            if self.target_pet:
                self.target_pet.is_being_chased = False
            self.target_pet = None
        dialog = self.generate_random_dialogue("auto_move")
        self.show_bubble(dialog)

    def trigger_random_behavior(self):
        if not self.is_random_behavior or self.is_dragging or not self.root.winfo_exists() or not self.is_alive:
            return
        behavior_type = random.choice(["speed_up", "flash_alpha", "teleport"])
        if behavior_type == "speed_up":
            old_speed_x = self.move_speed_x
            old_speed_y = self.move_speed_y
            self.move_speed_x *= 2
            self.move_speed_y *= 2
            self.main_root.after(2000, lambda: (setattr(self, "move_speed_x", old_speed_x),
                                           setattr(self, "move_speed_y", old_speed_y)))
        elif behavior_type == "flash_alpha":
            if not self.is_angry and not self.angry_dialog_shown:
                self.root.wm_attributes("-alpha", 0.5)
                self.main_root.after(300, lambda: self.root.wm_attributes("-alpha", 1.0))
                self.main_root.after(600, lambda: self.root.wm_attributes("-alpha", 0.5))
                self.main_root.after(900, lambda: self.root.wm_attributes("-alpha", 1.0))
        elif behavior_type == "teleport":
            new_x = random.randint(20, self.screen_width - self.root.winfo_width() - 20)
            new_y = random.randint(20, self.screen_height - self.root.winfo_height() - 20)
            self.root.geometry(f"+{new_x}+{new_y}")
        self.random_task_id = self.main_root.after(random.randint(5000, 15000), self.trigger_random_behavior)

    def toggle_random_behavior(self):
        self.is_random_behavior = not self.is_random_behavior
        if self.random_task_id:
            self.main_root.after_cancel(self.random_task_id)
            self.random_task_id = None
        if self.is_random_behavior:
            dialog = self.generate_random_dialogue("random")
            if not self.is_angry and not self.angry_dialog_shown:
                self.show_bubble(dialog)
            self.trigger_random_behavior()
        else:
            dialog = self.generate_random_dialogue("random")
            if not self.is_angry and not self.angry_dialog_shown:
                self.show_bubble(dialog)

    def resize_pet(self, width, height):
        self.pet_width = max(50, min(width, 400))
        self.pet_height = max(60, min(height, 400))
        self.preload_all_gifs()
        self.preload_angry_gif()
        self.init_current_gif()
        self.update_gif_display()
        dialog = self.generate_random_dialogue("resize")
        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(dialog)
        self.update_bubble_position()
        self.last_operate_time = time.time()

    def resize_pet_custom(self):
        custom_window = tk.Toplevel(self.main_root)
        custom_window.title("自定义宠物尺寸")
        custom_window.geometry("300x120")
        custom_window.wm_attributes("-topmost", True)

        tk.Label(custom_window, text="宽度（50-400）：").grid(row=0, column=0, padx=10, pady=10)
        width_entry = tk.Entry(custom_window, width=10)
        width_entry.grid(row=0, column=1, padx=10, pady=10)
        width_entry.insert(0, str(self.pet_width))

        tk.Label(custom_window, text="高度（60-400）：").grid(row=1, column=0, padx=10, pady=10)
        height_entry = tk.Entry(custom_window, width=10)
        height_entry.grid(row=1, column=1, padx=10, pady=10)
        height_entry.insert(0, str(self.pet_height))

        def confirm_custom():
            try:
                width = int(width_entry.get())
                height = int(height_entry.get())
                width = max(50, min(width, 400))
                height = max(60, min(height, 400))
                self.resize_pet(width, height)
                self.show_bubble(self.generate_random_dialogue("custom_size"))
                custom_window.destroy()
            except ValueError:
                self.show_bubble("请输入有效整数~")
                custom_window.destroy()

        tk.Button(custom_window, text="确认", command=confirm_custom).grid(row=2, column=0, columnspan=2, pady=10)

    def set_alpha(self, alpha_value):
        alpha_value = max(0.1, min(alpha_value, 1.0))
        self.root.wm_attributes("-alpha", alpha_value)
        dialog = self.generate_random_dialogue("alpha")
        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(dialog)
        self.last_operate_time = time.time()

    def set_alpha_custom(self):
        custom_window = tk.Toplevel(self.main_root)
        custom_window.title("自定义透明度")
        custom_window.geometry("250x100")
        custom_window.wm_attributes("-topmost", True)

        tk.Label(custom_window, text="透明度（0.1-1.0，默认1.0）：").pack(pady=10)
        alpha_entry = tk.Entry(custom_window, width=10)
        alpha_entry.pack()
        alpha_entry.insert(0, str(self.root.wm_attributes("-alpha")))

        def confirm_custom():
            try:
                alpha = float(alpha_entry.get())
                alpha = max(0.1, min(alpha, 1.0))
                self.set_alpha(alpha)
                self.show_bubble(self.generate_random_dialogue("custom_alpha"))
                custom_window.destroy()
            except ValueError:
                self.show_bubble("请输入有效数字~")
                custom_window.destroy()

        tk.Button(custom_window, text="确认", command=confirm_custom).pack(pady=10)

    def switch_gif(self):
        normal_keys = [k for k in self.preloaded_frames if k.startswith("normal_")]
        if len(normal_keys) < 2:
            if not self.is_angry and not self.angry_dialog_shown:
                self.show_bubble("没有更多GIF啦~")
            return
        current_frame_tuple = (self.gif_frames, self.frame_delays)
        current_key = next((k for k in normal_keys if self.preloaded_frames[k] == current_frame_tuple), normal_keys[0])
        current_idx = int(current_key.split("_")[1])
        next_idx = (current_idx + 1) % len(normal_keys)
        next_key = f"normal_{next_idx}"
        self.gif_frames, self.frame_delays = self.preloaded_frames[next_key]
        self.update_gif_display()
        self.play_gif_smooth()
        dialog = self.generate_random_dialogue("switch_gif")
        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(dialog)

    def prev_gif(self):
        normal_keys = [k for k in self.preloaded_frames if k.startswith("normal_")]
        if len(normal_keys) < 2:
            if not self.is_angry and not self.angry_dialog_shown:
                self.show_bubble("没有上一个GIF啦~")
            return
        current_frame_tuple = (self.gif_frames, self.frame_delays)
        current_key = next((k for k in normal_keys if self.preloaded_frames[k] == current_frame_tuple), normal_keys[0])
        current_idx = int(current_key.split("_")[1])
        prev_idx = (current_idx - 1) % len(normal_keys)
        prev_key = f"normal_{prev_idx}"
        self.gif_frames, self.frame_delays = self.preloaded_frames[prev_key]
        self.update_gif_display()
        self.play_gif_smooth()
        dialog = self.generate_random_dialogue("switch_gif")
        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(dialog)

    def pause_gif(self):
        self.is_gif_playing = False
        dialog = random.choice(["定格啦~ 📸", "不动咯~"])
        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(dialog)

    def resume_gif(self):
        self.is_gif_playing = True
        self.play_gif_smooth()
        dialog = random.choice(["动起来啦~ 🏃", "继续玩耍~"])
        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(dialog)

    def enable_auto_move(self):
        self.is_auto_move = True
        dialog = self.generate_random_dialogue("auto_move")
        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(dialog)

    def disable_auto_move(self):
        self.is_auto_move = False
        # 关闭自动移动时，同时关闭追逐模式
        self.is_chasing = False
        if self.target_pet:
            self.target_pet.is_being_chased = False
        self.target_pet = None
        dialog = self.generate_random_dialogue("auto_move")
        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(dialog)

    def toggle_topmost(self):
        self.is_topmost = not self.is_topmost
        self.root.wm_attributes("-topmost", self.is_topmost)
        if self.is_topmost:
            dialog = "我置顶啦，不会被挡住~ 😎"
        else:
            dialog = "我取消置顶啦，可被其他窗口覆盖~ 🤫"
        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble(dialog)

    def create_new_pet(self):
        """新建宠物：使用独立GIF配置，避免重复"""
        # ========== 关键修改：使用新的GIF路径（需提前准备） ==========
        # 示例：第二套宠物的GIF路径（替换为你实际的第二套资源路径）
        new_gif_list = [
            "pet2.gif",  # 第二套普通GIF
            "pet2_2.gif"
        ]
        new_angry_gif = "angry_pet2.gif"  # 第二套生气GIF

        # 固定默认尺寸
        default_width = 150
        default_height = 180
        new_width = max(default_width, 50)
        new_height = max(default_height, 60)

        # 尺寸校验
        max_possible_width = self.screen_width - 40
        max_possible_height = self.screen_height - 40
        new_width = min(new_width, max_possible_width)
        new_height = min(new_height, max_possible_height)

        # 位置校验：避免固定顶部
        max_x = self.screen_width - new_width - 40
        max_y = self.screen_height - new_height - 40
        max_x = max(max_x, 20)
        max_y = max(max_y, 20)
        new_x = random.randint(20, max_x)
        new_y = random.randint(20, max_y)

        # 异步创建新宠物（传入主窗口引用）
        def async_create_pet():
            new_pet = SmoothGifPet(
                self.main_root,
                new_gif_list,
                new_angry_gif,
                pet_width=new_width,
                pet_height=new_height
            )
            # 若实例创建成功（非重复），设置初始位置
            if new_pet.is_alive:
                new_pet.root.geometry(f"+{int(new_x)}+{int(new_y)}")

        self.main_root.after(100, async_create_pet)

        if not self.is_angry and not self.angry_dialog_shown:
            self.show_bubble("新宠物来啦，我们一起玩耍~ 🐾")

    def load_config(self):
        if os.path.exists(self.config_path):
            try:
                with open(self.config_path, "r", encoding="utf-8") as f:
                    config = json.load(f)
                self.current_gif_idx = config.get("current_gif_idx", 0)
                self.is_auto_move = config.get("is_auto_move", True)
                self.pet_width = max(config.get("pet_width", 150), 50)
                self.pet_height = max(config.get("pet_height", 180), 60)
                alpha = config.get("alpha", 1.0)
                self.root.wm_attributes("-alpha", alpha)
                self.is_random_behavior = config.get("is_random_behavior", False)
                self.bubble_duration = config.get("bubble_duration", 3000)
                self.inertia_coeff = config.get("inertia_coeff", 0.8)
                self.damping_coeff = config.get("damping_coeff", 0.95)
                self.bounce_coeff = config.get("bounce_coeff", 0.8)
                # 加载追逐相关配置
                self.chase_speed_multiplier = config.get("chase_speed_multiplier", 1.5)
                self.chase_distance_threshold = config.get("chase_distance_threshold", 200)
                # ========== 新增：加载饥饿值 ==========
                self.hunger_value = max(0, min(100, config.get("hunger_value", 50)))
                print("配置加载成功！")
            except Exception as e:
                print(f"加载配置失败：{e}")

    def save_config(self):
        config = {
            "current_gif_idx": self.current_gif_idx,
            "is_auto_move": self.is_auto_move,
            "pet_width": self.pet_width,
            "pet_height": self.pet_height,
            "alpha": self.root.wm_attributes("-alpha"),
            "is_random_behavior": self.is_random_behavior,
            "bubble_duration": self.bubble_duration,
            "inertia_coeff": self.inertia_coeff,
            "damping_coeff": self.damping_coeff,
            "bounce_coeff": self.bounce_coeff,
            # 保存追逐相关配置
            "chase_speed_multiplier": self.chase_speed_multiplier,
            "chase_distance_threshold": self.chase_distance_threshold,
            # ========== 新增：保存饥饿值 ==========
            "hunger_value": self.hunger_value
        }
        try:
            with open(self.config_path, "w", encoding="utf-8") as f:
                json.dump(config, f, ensure_ascii=False, indent=2)
            print("配置保存成功！")
        except Exception as e:
            print(f"保存配置失败：{e}")

    def save_and_quit(self):
        self.save_config()
        dialog = self.generate_random_dialogue("quit")
        self.show_bubble(dialog)

        def destroy_pet():
            self.is_alive = False
            # 新增：释放语音相关资源，避免堆损坏
            self.voice_enabled = False  # 停止语音识别线程
            if self.tts_engine:  # 若TTS引擎有效，停止它
                self.tts_engine.stop()
            # 从全局列表中移除实例和GIF哈希
            if self in PET_INSTANCES:
                PET_INSTANCES.remove(self)
            if self.gif_combination_hash in PET_GIF_HASHES:
                PET_GIF_HASHES.remove(self.gif_combination_hash)
            # 取消其他宠物对当前宠物的追逐
            for pet in PET_INSTANCES:
                if pet.target_pet is self:
                    pet.is_chasing = False
                    pet.target_pet = None
                    pet.move_speed_x = pet.base_move_speed_x
                    pet.move_speed_y = pet.base_move_speed_y
            self.bubble_window.destroy()
            self.root.destroy()

        self.main_root.after(self.bubble_duration, destroy_pet)

    # ========== 新增：右键菜单添加追逐模式开关 ==========
    def show_right_menu(self, event):
        right_menu = tk.Menu(self.root, tearoff=0)

        # GIF控制
        gif_menu = tk.Menu(right_menu, tearoff=0)
        gif_menu.add_command(label="上一个GIF", command=self.prev_gif)
        gif_menu.add_command(label="下一个GIF", command=self.switch_gif)
        gif_menu.add_separator()
        gif_menu.add_command(label="暂停GIF播放", command=self.pause_gif)
        gif_menu.add_command(label="继续GIF播放", command=self.resume_gif)
        right_menu.add_cascade(label="GIF控制", menu=gif_menu)
        right_menu.add_separator()

        # 气泡时长设置
        bubble_menu = tk.Menu(right_menu, tearoff=0)
        bubble_menu.add_command(label="1秒", command=self.set_bubble_duration_1s)
        bubble_menu.add_command(label="3秒（默认）", command=self.set_bubble_duration_3s)
        bubble_menu.add_command(label="5秒", command=self.set_bubble_duration_5s)
        bubble_menu.add_command(label="10秒", command=self.set_bubble_duration_10s)
        bubble_menu.add_separator()
        bubble_menu.add_command(label="手动输入自定义时长", command=self.set_bubble_duration_custom)
        right_menu.add_cascade(label="气泡时长设置", menu=bubble_menu)
        right_menu.add_separator()

        # 切换置顶状态
        right_menu.add_command(label="切换置顶状态", command=self.toggle_topmost)
        right_menu.add_separator()

        # 自动移动开关
        if self.is_auto_move:
            right_menu.add_command(label="固定窗口（关闭自由移动）", command=self.disable_auto_move)
        else:
            right_menu.add_command(label="自由移动（开启自动移动）", command=self.enable_auto_move)
        right_menu.add_separator()

        # 新建宠物
        right_menu.add_command(label="新建宠物", command=self.create_new_pet)
        right_menu.add_separator()

        # 随机行为开关
        if self.is_random_behavior:
            right_menu.add_command(label="关闭随机行为", command=self.toggle_random_behavior)
        else:
            right_menu.add_command(label="开启随机行为", command=self.toggle_random_behavior)
        right_menu.add_separator()

        # 新增：追逐模式开关
        if self.is_chasing:
            right_menu.add_command(label="关闭追逐模式", command=self.toggle_chase_mode)
        else:
            right_menu.add_command(label="开启追逐模式", command=self.toggle_chase_mode)
        right_menu.add_separator()

        # ========== 新增：喂食子菜单 ==========
        feed_menu = tk.Menu(right_menu, tearoff=0)
        # 遍历喂食道具，动态添加菜单选项
        for food_name in self.feed_items.keys():
            feed_menu.add_command(label=f"喂食：{food_name}", command=lambda fn=food_name: self.feed_pet(fn))
        # 新增：查看当前饥饿值
        feed_menu.add_separator()
        feed_menu.add_command(
            label=f"当前饥饿值：{int(self.hunger_value)}（100=饱腹）",
            command=lambda: self.show_bubble(f"我的饥饿值现在是{int(self.hunger_value)}哦~ 🥰")
        )
        right_menu.add_cascade(label="宠物喂食", menu=feed_menu)
        right_menu.add_separator()
        # ========== 新增：QQ音乐手动控制 ==========
        # ========== 替换原有QQ音乐代码，添加控制子菜单 ==========
        # QQ音乐控制子菜单
        qq_music_menu = tk.Menu(right_menu, tearoff=0)
        qq_music_menu.add_command(label="启动QQ音乐", command=self.auto_play_qq_music)
        qq_music_menu.add_command(label="暂停/播放切换", command=self.toggle_qq_music_play)
        qq_music_menu.add_command(label="上一首", command=self.qq_music_prev_song)
        qq_music_menu.add_command(label="下一首", command=self.qq_music_next_song)
        right_menu.add_cascade(label="QQ音乐控制", menu=qq_music_menu)
        right_menu.add_separator()

        # ========== 新增：语音控制菜单选项 ==========
        right_menu.add_command(label="切换语音控制", command=self.toggle_voice_control)
        right_menu.add_separator()
        # ========== 语音控制选项结束 ==========

        # 宠物尺寸调节
        size_menu = tk.Menu(right_menu, tearoff=0)
        size_menu.add_command(label="小型（100x120）", command=lambda: self.resize_pet(100, 120))
        size_menu.add_command(label="中型（150x180）", command=lambda: self.resize_pet(150, 180))
        size_menu.add_command(label="大型（200x240）", command=lambda: self.resize_pet(200, 240))
        size_menu.add_separator()
        size_menu.add_command(label="手动输入自定义尺寸", command=self.resize_pet_custom)
        right_menu.add_cascade(label="调节宠物大小", menu=size_menu)
        right_menu.add_separator()

        # 透明度调节
        alpha_menu = tk.Menu(right_menu, tearoff=0)
        alpha_menu.add_command(label="高透明（50%）", command=lambda: self.set_alpha(0.5))
        alpha_menu.add_command(label="中等透明（80%）", command=lambda: self.set_alpha(0.8))
        alpha_menu.add_command(label="不透明（100%）", command=lambda: self.set_alpha(1.0))
        alpha_menu.add_separator()
        alpha_menu.add_command(label="手动输入自定义透明度", command=self.set_alpha_custom)
        right_menu.add_cascade(label="调节透明度", menu=alpha_menu)
        right_menu.add_separator()

        # 物理反馈强度设置
        physics_menu = tk.Menu(right_menu, tearoff=0)
        physics_menu.add_command(label="低惯性（0.3）", command=lambda: self.set_physics_coeff(inertia=0.3))
        physics_menu.add_command(label="默认惯性（0.8）", command=lambda: self.set_physics_coeff(inertia=0.8))
        physics_menu.add_command(label="高惯性（1.5）", command=lambda: self.set_physics_coeff(inertia=1.5))
        physics_menu.add_separator()
        physics_menu.add_command(label="低阻尼（0.8）", command=lambda: self.set_physics_coeff(damping=0.8))
        physics_menu.add_command(label="默认阻尼（0.95）", command=lambda: self.set_physics_coeff(damping=0.95))
        physics_menu.add_command(label="高阻尼（0.99）", command=lambda: self.set_physics_coeff(damping=0.99))
        physics_menu.add_separator()
        physics_menu.add_command(label="低反弹（0.3）", command=lambda: self.set_physics_coeff(bounce=0.3))
        physics_menu.add_command(label="默认反弹（0.8）", command=lambda: self.set_physics_coeff(bounce=0.8))
        physics_menu.add_command(label="高反弹（1.2）", command=lambda: self.set_physics_coeff(bounce=1.2))
        physics_menu.add_separator()
        physics_menu.add_command(label="手动输入自定义强度", command=self.set_physics_custom)
        right_menu.add_cascade(label="物理反馈强度设置", menu=physics_menu)
        right_menu.add_separator()

        # 退出程序
        right_menu.add_command(label="退出程序", command=self.save_and_quit)

        # 显示菜单
        right_menu.post(event.x_root, event.y_root)

# 程序入口
if __name__ == "__main__":
    # 用try包裹整个程序入口逻辑
    try:
        # 1. GIF路径配置
        MY_GIF_LIST = ["pet1.gif", "pet2.gif"]  # 可替换为你的路径
        ANGRY_GIF_PATH = "angry_pet.gif"

        # 2. 创建主窗口
        main_root = tk.Tk()
        main_root.withdraw()  # 隐藏主窗口
        main_root.title("桌面宠物管理")

        # 3. 创建宠物实例
        first_pet = None
        try:
            first_pet = SmoothGifPet(
                main_root=main_root,
                gif_path_list=MY_GIF_LIST,
                angry_gif_path=ANGRY_GIF_PATH,
                pet_width=150,
                pet_height=180
            )
            if first_pet.is_alive:
                print("桌面宠物创建成功！")
            else:
                print("宠物创建失败：资源缺失或配置错误")
        except Exception as e:
            print(f"宠物实例化失败：{e}")

        # 4. 启动主循环（程序运行的核心）
        main_root.mainloop()

    # 捕获手动终止异常（Ctrl+C）
    except KeyboardInterrupt:
        print("\n程序已被手动终止（Ctrl+C）")
    # 捕获其他未知异常
    except Exception as e:
        print(f"程序运行时发生未知错误：{e}")
    # 无论是否异常，最终都会执行（可选）
    finally:
        print("程序已退出")
