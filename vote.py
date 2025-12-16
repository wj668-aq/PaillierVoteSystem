from flask import Flask, render_template, request, jsonify, redirect, url_for, session
import json
import os
import hashlib
import secrets
import random
from datetime import datetime
from math import gcd
from jinja2 import Undefined
from functools import wraps

app = Flask(__name__)
app.secret_key = os.environ.get('SECRET_KEY', 'secure_election_system_secret_key_2025')


#记录投票方式为字典
#票数用列表存储，初始为加密的0，新建候选人即往列表中添加一个加密的0
#哈希验证投票的数据是否被篡改，包括投票人，选举人序列号，时间

# ==================== Paillier加密系统 ====================

class PaillierEncryption:
    """Paillier同态加密系统"""

    @staticmethod
    def generate_keypair(bit_length=512):
        """生成Paillier密钥对"""
        # 使用小素数用于演示
        p = 61
        q = 53
        n = p * q
        n_sq = n * n
        lambda_val = (p - 1) * (q - 1)

        g = n + 1
        mu = pow(lambda_val, -1, n)

        public_key = (n, g)
        private_key = (lambda_val, mu)

        return public_key, private_key

    @staticmethod
    def encrypt(public_key, plaintext, r=None):
        """加密明文"""
        n, g = public_key
        n_sq = n * n

        if r is None:
            while True:
                r = random.randint(1, n - 1)
                if gcd(r, n) == 1:
                    break

        c = (pow(g, plaintext, n_sq) * pow(r, n, n_sq)) % n_sq
        return c

    @staticmethod
    def decrypt(private_key, public_key, ciphertext):
        """解密密文"""
        lambda_val, mu = private_key
        n, g = public_key
        n_sq = n * n

        u = pow(ciphertext, lambda_val, n_sq)
        l_val = (u - 1) // n
        plaintext = (l_val * mu) % n

        return plaintext

    @staticmethod
    def add_ciphertexts(public_key, ciphertext1, ciphertext2):
        """同态加法：E(m1) * E(m2) = E(m1 + m2)"""
        n, g = public_key
        n_sq = n * n
        return (ciphertext1 * ciphertext2) % n_sq


# ==================== 数据存储类 ====================

class SecureElectionData:
    def __init__(self, data_file='election_data.json'):
        self.data_file = data_file
        self.data = self.load_data()

    def load_data(self):
        """加载选举数据"""
        try:
            with open(self.data_file, 'r', encoding='utf-8') as f:
                return json.load(f)
        except (FileNotFoundError, json.JSONDecodeError):
            return {
                'elections': {},
                'current_election_id': None,
                'key_shares': {},
                'secret_shares': {}
            }

    def save_data(self):
        """保存选举数据"""
        try:
            with open(self.data_file, 'w', encoding='utf-8') as f:
                json.dump(self.data, f, ensure_ascii=False, indent=2)
            return True
        except Exception as e:
            print(f"保存数据错误: {e}")
            return False

    def create_election(self, title, start_time='', end_time=''):
        """创建新的选举"""
        try:
            election_id = secrets.token_hex(8)

            new_election = {
                'id': election_id,
                'title': title,
                'start_time': start_time,
                'end_time': end_time,
                'candidates': [],
                'status': 'not_started',
                'votes': [],
                'crypto_setup': None,
                'encrypted_tallies': [],
                'partial_decryptions': {},
                'final_results': None,
                'is_public': False,  # 是否公示结果
                'created_at': datetime.now().isoformat(),
                'verification_hashes': {},
                'secret_shares': {},
                'public_at': None,  # 公示时间
                'total_votes': 0
            }

            self.data['elections'][election_id] = new_election
            self.data['current_election_id'] = election_id

            if self.save_data():
                return election_id
            return None
        except Exception as e:
            print(f"创建选举错误: {e}")
            return None

    def get_current_election(self):
        """获取当前选举"""
        if self.data['current_election_id'] and self.data['current_election_id'] in self.data['elections']:
            return self.data['elections'][self.data['current_election_id']]
        return None

    def update_election(self, election_id, updates):
        """更新选举数据"""
        try:
            if election_id in self.data['elections']:
                self.data['elections'][election_id].update(updates)
                return self.save_data()
            return False
        except Exception as e:
            print(f"更新选举错误: {e}")
            return False

    def add_candidate(self, name):
        """添加候选人"""
        try:
            election = self.get_current_election()
            if not election or not election.get('id'):
                return False

            candidates = election.get('candidates', [])
            if name in candidates:
                return False

            candidates.append(name)
            return self.update_election(election['id'], {'candidates': candidates})
        except Exception as e:
            print(f"添加候选人错误: {e}")
            return False

    def initialize_system(self):
        """初始化加密系统"""
        try:
            election = self.get_current_election()
            if not election or not election.get('id'):
                return False, "没有活动的选举"

            candidates = election.get('candidates', [])
            if len(candidates) < 2:
                return False, f"需要至少2名候选人，当前有{len(candidates)}名候选人"

            # 生成Paillier密钥对
            public_key, private_key = PaillierEncryption.generate_keypair()

            # 为每个候选人初始化加密计数器（初始值为0）
            encrypted_counters = [PaillierEncryption.encrypt(public_key, 0) for _ in range(len(candidates))]

            crypto_setup = {
                'public_key': public_key,
                'private_key': private_key,
                'encrypted_results': encrypted_counters
            }

            success = self.update_election(election['id'], {
                'crypto_setup': crypto_setup,
                'encrypted_tallies': encrypted_counters,
                'status': 'ready'
            })

            if success:
                return True, "Paillier加密系统初始化成功"
            else:
                return False, "更新选举数据失败"
        except Exception as e:
            print(f"初始化系统错误: {e}")
            return False, f"系统初始化过程中发生错误: {str(e)}"

    def add_vote(self, voter_id, candidate_index):
        """添加加密投票"""
        try:
            print("=== 开始处理投票 ===")
            election = self.get_current_election()
            if not election or not election.get('id'):
                print("错误：没有活动的选举")
                return False, "没有活动的选举"

            # 检查选举状态
            if election.get('status') in ['finished', 'revealed']:
                print("错误：选举已结束")
                return False, "选举已结束，无法投票"

            # 获取候选人列表
            candidates = election.get('candidates', [])
            print(f"候选人列表: {candidates}")
            print(f"候选人数量: {len(candidates)}")
            print(f"传入的 candidate_index: {candidate_index}, 类型: {type(candidate_index)}")

            # 验证候选人索引
            try:
                candidate_index = int(candidate_index)
                print(f"转换后的 candidate_index: {candidate_index}")
            except (ValueError, TypeError) as e:
                print(f"转换 candidate_index 错误: {e}")
                return False, "无效的候选人索引格式"

            if candidate_index < 0 or candidate_index >= len(candidates):
                print(f"错误：候选人索引越界")
                return False, f"无效的候选人选择。请选择0到{len(candidates) - 1}之间的编号"

            if len(candidates) == 0:
                print("错误：没有候选人")
                return False, "选举中没有候选人"

            candidate_name = candidates[candidate_index]
            print(f"选择的候选人: {candidate_name} (索引: {candidate_index})")

            # 检查是否已投票
            for vote in election.get('votes', []):
                if vote.get('voter_id') == voter_id:
                    print(f"错误：用户 {voter_id} 已投票")
                    return False, "您已经投过票了"

            # 统一为一票制
            weight = 1

            # 生成投票哈希
            timestamp = datetime.now().isoformat()
            vote_hash = self.generate_vote_hash(voter_id, candidate_index, timestamp)

            # 记录投票
            vote_record = {
                'voter_id': voter_id,
                'candidate_index': candidate_index,
                'candidate_name': candidate_name,
                'weight': weight,
                'timestamp': timestamp,
                'vote_hash': vote_hash
            }

            votes = election.get('votes', [])
            votes.append(vote_record)

            # 保存验证哈希
            verification_hashes = election.get('verification_hashes', {})
            verification_hashes[vote_hash] = {
                'voter_id': voter_id,
                'candidate_index': candidate_index,
                'timestamp': timestamp
            }

            success = self.update_election(election['id'], {
                'votes': votes,
                'verification_hashes': verification_hashes,
                'status': 'voting'
            })

            if success:
                print(f"投票成功！候选人: {candidate_name} (索引: {candidate_index})")
                return True, "投票成功"
            else:
                print("投票记录失败")
                return False, "投票记录失败"

        except Exception as e:
            print(f"添加投票错误: {e}")
            return False, f"投票过程中发生错误: {str(e)}"

    def generate_vote_hash(self, voter_id, candidate_index, timestamp):
        """生成投票验证哈希"""
        data = f"{voter_id}_{candidate_index}_{timestamp}".encode()
        return hashlib.sha256(data).hexdigest()

    def end_voting_and_count(self):
        """结束投票并进行Paillier同态计票"""
        try:
            election = self.get_current_election()
            if not election:
                return False, "没有活动的选举", None

            if election.get('status') != 'voting':
                return False, "选举不在投票中，无法结束", None

            votes = election.get('votes', [])
            if len(votes) == 0:
                return False, "没有投票记录，无法计票", None

            crypto_setup = election.get('crypto_setup')
            if not crypto_setup:
                return False, "加密系统未初始化", None

            public_key = crypto_setup['public_key']
            encrypted_tallies = election.get('encrypted_tallies', [])

            # 使用Paillier同态加密进行计票
            for vote in votes:
                candidate_index = vote.get('candidate_index', 0)
                weight = vote.get('weight', 1)

                if candidate_index < len(encrypted_tallies):
                    # 对选择的候选人票数加1（同态加法）
                    encrypted_vote = PaillierEncryption.encrypt(public_key, weight)
                    encrypted_tallies[candidate_index] = PaillierEncryption.add_ciphertexts(
                        public_key, encrypted_tallies[candidate_index], encrypted_vote
                    )

            # 生成秘密共享分片
            private_key = crypto_setup['private_key']
            lambda_val, mu = private_key

            # 生成两个共享分片
            share1 = random.randint(1, lambda_val - 1)
            share2 = lambda_val - share1

            # 保存密钥分片
            if 'key_shares' not in self.data:
                self.data['key_shares'] = {}

            self.data['key_shares'][election['id']] = {
                'teacher_share': share1,
                'secretary_share': share2,
                'mu': mu,
                'public_key': public_key
            }

            # 保存共享分片信息
            secret_shares = {
                'teacher_share': str(share1),
                'secretary_share': str(share2),
                'public_key': str(public_key)
            }

            success = self.update_election(election['id'], {
                'encrypted_tallies': encrypted_tallies,
                'status': 'finished',
                'is_public': False,  # 默认不公示
                'secret_shares': secret_shares,
                'finished_at': datetime.now().isoformat(),
                'total_votes': len(votes)
            })

            if success:
                return True, "投票结束并完成Paillier同态计票", secret_shares
            else:
                return False, "更新选举数据失败", None

        except Exception as e:
            print(f"结束投票计票错误: {e}")
            return False, f"计票过程中发生错误: {str(e)}", None

    def partial_decrypt(self, share_owner, share_value):
        """部分解密"""
        try:
            election = self.get_current_election()
            if not election:
                return False, "没有活动的选举", None

            if election.get('status') != 'finished':
                return False, "选举尚未结束计票", None

            key_shares = self.data.get('key_shares', {}).get(election['id'], {})
            if not key_shares:
                return False, "未找到密钥分片", None

            # 验证共享分片
            if share_owner == 'teacher':
                stored_share = key_shares.get('teacher_share')
            elif share_owner == 'secretary':
                stored_share = key_shares.get('secretary_share')
            else:
                return False, "无效的分片所有者", None

            if str(share_value) != str(stored_share):
                return False, "共享分片验证失败", None

            # 执行部分解密
            crypto_setup = election.get('crypto_setup')
            public_key = crypto_setup['public_key']
            encrypted_tallies = election.get('encrypted_tallies', [])
            mu = key_shares.get('mu')

            partial_decryptions = []
            for ciphertext in encrypted_tallies:
                # 部分解密：c^lambda mod n^2
                n, g = public_key
                n_sq = n * n
                partial_dec = pow(ciphertext, share_value, n_sq)
                partial_decryptions.append(partial_dec)

            # 保存部分解密结果
            partial_decryptions_dict = election.get('partial_decryptions', {})
            partial_decryptions_dict[share_owner] = partial_decryptions

            success = self.update_election(election['id'], {
                'partial_decryptions': partial_decryptions_dict
            })

            if success:
                return True, f"{share_owner}部分解密完成", partial_decryptions
            else:
                return False, "保存部分解密结果失败", None

        except Exception as e:
            print(f"部分解密错误: {e}")
            return False, f"部分解密过程中发生错误: {str(e)}", None

    def combine_decryptions(self):
        """合并部分解密结果得到最终结果"""
        try:
            election = self.get_current_election()
            if not election:
                return False, "没有活动的选举", None

            partial_decryptions = election.get('partial_decryptions', {})
            if 'teacher' not in partial_decryptions or 'secretary' not in partial_decryptions:
                return False, "需要导员和团支书双方的部分解密结果", None

            crypto_setup = election.get('crypto_setup')
            public_key = crypto_setup['public_key']
            key_shares = self.data.get('key_shares', {}).get(election['id'], {})
            mu = key_shares.get('mu')

            n, g = public_key
            n_sq = n * n

            # 合并部分解密结果
            final_results = {}
            candidates = election.get('candidates', [])
            teacher_partial = partial_decryptions['teacher']
            secretary_partial = partial_decryptions['secretary']

            for i, candidate in enumerate(candidates):
                if i < len(teacher_partial) and i < len(secretary_partial):
                    # 合并部分解密：c^(lambda1 + lambda2) mod n^2
                    combined = (teacher_partial[i] * secretary_partial[i]) % n_sq

                    # 最终解密：L(c^lambda mod n^2) * mu mod n
                    u = combined
                    l_val = (u - 1) // n
                    plaintext = (l_val * mu) % n

                    final_results[candidate] = plaintext

            success = self.update_election(election['id'], {
                'final_results': final_results,
                'status': 'revealed',  # 更新状态为已揭示
                'revealed_at': datetime.now().isoformat()
            })

            if success:
                return True, "最终结果解密完成", final_results
            else:
                return False, "保存最终结果失败", None

        except Exception as e:
            print(f"合并解密错误: {e}")
            return False, f"合并解密过程中发生错误: {str(e)}", None

    def make_results_public(self):
        """公示选举结果"""
        try:
            print("DEBUG: 开始公示选举结果")

            election = self.get_current_election()
            if not election:
                print("DEBUG: 没有找到当前选举")
                return False, "没有活动的选举"

            print(f"DEBUG: 当前选举状态: {election.get('status')}")
            print(f"DEBUG: 是否有最终结果: {bool(election.get('final_results'))}")
            print(f"DEBUG: 当前公示状态: {election.get('is_public')}")

            if election.get('status') != 'revealed':
                print("DEBUG: 选举结果尚未揭示，无法公示")
                return False, "选举结果尚未揭示，无法公示"

            if not election.get('final_results'):
                print("DEBUG: 没有最终结果数据")
                return False, "没有找到选举结果数据，无法公示"

            # 更新公示状态
            updates = {
                'is_public': True,
                'public_at': datetime.now().isoformat()
            }

            print(f"DEBUG: 准备更新公示数据: {updates}")

            success = self.update_election(election['id'], updates)

            if success:
                print("DEBUG: 公示成功")
                # 重新加载数据确认更新
                updated_election = self.get_current_election()
                print(f"DEBUG: 更新后公示状态: {updated_election.get('is_public')}")
                return True, "选举结果已公示"
            else:
                print("DEBUG: 公示失败，更新数据失败")
                return False, "公示结果失败"

        except Exception as e:
            print(f"DEBUG: 公示结果错误: {e}")
            return False, f"公示结果过程中发生错误: {str(e)}"

    def verify_vote(self, vote_hash, voter_id):
        """验证投票"""
        try:
            election = self.get_current_election()
            if not election:
                return False, "没有活动的选举"

            vote_data = election.get('verification_hashes', {}).get(vote_hash)
            if not vote_data or vote_data.get('voter_id') != voter_id:
                return False, "未找到匹配的投票记录"

            for vote in election.get('votes', []):
                if (vote.get('voter_id') == voter_id and
                        vote.get('vote_hash') == vote_hash):
                    return self.verify_vote_integrity(vote_hash, voter_id, vote.get('timestamp'), vote)

            return False, "投票记录不完整"
        except Exception as e:
            print(f"验证投票错误: {e}")
            return False, f"投票验证过程中发生错误: {str(e)}"

    def verify_vote_integrity(self, vote_hash, voter_id, timestamp, vote_record):
        """验证投票完整性"""
        try:
            expected_hash = self.generate_vote_hash(voter_id, vote_record.get('candidate_index', 0), timestamp)
            if vote_hash == expected_hash:
                return True, "投票验证成功"
            else:
                return False, f"投票验证失败：哈希不匹配。期望：{expected_hash}，实际：{vote_hash}"
        except Exception as e:
            print(f"验证投票完整性错误: {e}")
            return False, f"验证投票完整性错误: {str(e)}"


# ==================== Flask应用和路由 ====================

election_db = SecureElectionData()


def safe_tojson(data):
    """安全地将数据转换为JSON"""
    if data is None or isinstance(data, Undefined):
        return '{}'

    def make_serializable(obj):
        if isinstance(obj, (dict, list, str, int, float, bool, type(None))):
            return obj
        elif hasattr(obj, 'isoformat'):
            return obj.isoformat()
        else:
            return str(obj)

    def process_value(value):
        if isinstance(value, dict):
            return {k: process_value(v) for k, v in value.items()}
        elif isinstance(value, list):
            return [process_value(item) for item in value]
        else:
            return make_serializable(value)

    try:
        processed_data = process_value(data)
        return json.dumps(processed_data, ensure_ascii=False)
    except Exception as e:
        print(f"JSON序列化错误: {e}")
        return '{}'


@app.route('/')
def index():
    return redirect(url_for('admin'))


@app.route('/admin', methods=['GET', 'POST'])
def admin():
    """管理员页面"""
    if request.method == 'POST':
        action = request.form.get('action')

        if action == 'create_election':
            title = request.form.get('title', '班级班长选举').strip()
            if not title:
                return jsonify({'success': False, 'message': '请输入选举标题'})

            election_id = election_db.create_election(title)
            if election_id:
                return jsonify({
                    'success': True,
                    'message': '新的选举活动创建成功！候选人列表已清空',
                    'election_id': election_id
                })
            else:
                return jsonify({'success': False, 'message': '创建选举活动失败'})

        elif action == 'add_candidate':
            candidate_name = request.form.get('name', '').strip()
            if not candidate_name:
                return jsonify({'success': False, 'message': '请输入候选人姓名'})

            success = election_db.add_candidate(candidate_name)
            if success:
                current_election = election_db.get_current_election()
                return jsonify({
                    'success': True,
                    'candidates': current_election.get('candidates', []) if current_election else [],
                    'message': '候选人添加成功！'
                })
            else:
                return jsonify({'success': False, 'message': '添加候选人失败'})

        elif action == 'initialize_system':
            success, message = election_db.initialize_system()
            return jsonify({'success': success, 'message': message})

        elif action == 'end_voting':
            success, message, shares = election_db.end_voting_and_count()
            if success:
                return jsonify({
                    'success': True,
                    'message': message,
                    'shares': shares
                })
            else:
                return jsonify({'success': False, 'message': message})

    current_election = election_db.get_current_election() or {}
    election_data_json = safe_tojson(current_election)

    return render_template('admin.html',
                           election_data=current_election,
                           election_data_json=election_data_json)


@app.route('/vote', methods=['GET', 'POST'])
def vote():
    """投票页面"""
    current_election = election_db.get_current_election()

    if request.method == 'POST':
        if not request.is_json:
            return jsonify({'success': False, 'message': '请求必须是JSON格式'}), 400

        data = request.get_json()
        if not data:
            return jsonify({'success': False, 'message': '无效的JSON数据'}), 400

        voter_id = data.get('voter_id', '').strip()
        candidate_index = data.get('candidate_index')

        if candidate_index is None:
            return jsonify({'success': False, 'message': '请选择有效的候选人'})

        try:
            candidate_index = int(candidate_index)
        except (ValueError, TypeError):
            return jsonify({'success': False, 'message': '无效的候选人索引格式'})

        if not voter_id:
            return jsonify({'success': False, 'message': '请输入学号/工号'})

        success, message = election_db.add_vote(voter_id, candidate_index)
        if success:
            current_election = election_db.get_current_election()
            if current_election and current_election.get('votes'):
                last_vote = current_election['votes'][-1]
                return jsonify({
                    'success': True,
                    'vote_hash': last_vote.get('vote_hash'),
                    'weight': last_vote.get('weight', 1),
                    'message': f'投票成功！您的投票凭证是：{last_vote.get("vote_hash")}'
                })
            else:
                return jsonify({'success': False, 'message': '投票失败'})
        else:
            return jsonify({'success': False, 'message': message})

    current_election = current_election or {}
    current_election.setdefault('secret_shares', {})
    election_data_json = safe_tojson(current_election)
    return render_template('vote.html',
                           election_data=current_election,
                           election_data_json=election_data_json)


@app.route('/result')
def result():
    """结果显示页面"""
    current_election = election_db.get_current_election() or {}
    election_data_json = safe_tojson(current_election)
    return render_template('result.html',
                           election_data=current_election,
                           election_data_json=election_data_json)


@app.route('/reveal', methods=['GET', 'POST'])
def reveal_results():
    """结果揭示页面"""
    if request.method == 'POST':
        action = request.form.get('action')
        print(f"DEBUG: 收到揭示请求，action: {action}")

        if action == 'partial_decrypt':
            share_owner = request.form.get('share_owner')
            share_value = request.form.get('share_value', '').strip()

            print(f"DEBUG: 部分解密请求 - 所有者: {share_owner}, 分片: {share_value}")

            if not share_owner:
                print("DEBUG: 未指定分片所有者")
                return jsonify({'success': False, 'message': '请选择分片所有者'})
            if not share_value:
                print("DEBUG: 未输入共享分片")
                return jsonify({'success': False, 'message': '请输入共享分片'})

            try:
                share_value = int(share_value)
                print(f"DEBUG: 转换后的分片值: {share_value}")
            except ValueError:
                print("DEBUG: 分片值不是有效数字")
                return jsonify({'success': False, 'message': '共享分片必须是数字'})

            success, message, partial_results = election_db.partial_decrypt(share_owner, share_value)
            print(f"DEBUG: 部分解密结果 - 成功: {success}, 消息: {message}")

            if success:
                return jsonify({
                    'success': True,
                    'message': message,
                    'partial_results': partial_results
                })
            else:
                return jsonify({'success': False, 'message': message})

        elif action == 'combine_decryptions':
            print("DEBUG: 收到合并解密请求")
            success, message, final_results = election_db.combine_decryptions()
            return jsonify({
                'success': success,
                'message': message,
                'final_results': final_results
            })

        elif action == 'make_public':
            print("DEBUG: 收到公示请求")
            success, message = election_db.make_results_public()
            print(f"DEBUG: 公示结果 - 成功: {success}, 消息: {message}")
            return jsonify({'success': success, 'message': message})

    current_election = election_db.get_current_election() or {}
    election_data_json = safe_tojson(current_election)
    return render_template('reveal.html',
                           election_data=current_election,
                           election_data_json=election_data_json)

@app.route('/verify', methods=['GET', 'POST'])
def verify_vote():
    """投票验证页面"""
    if request.method == 'POST':
        vote_hash = request.form.get('vote_hash', '').strip()
        voter_id = request.form.get('voter_id', '').strip()

        if not vote_hash:
            return jsonify({'success': False, 'message': '请输入投票凭证哈希值'})
        if not voter_id:
            return jsonify({'success': False, 'message': '请输入您的学号/工号'})

        is_valid, message = election_db.verify_vote(vote_hash, voter_id)
        if is_valid:
            return jsonify({'success': True, 'message': message})
        else:
            return jsonify({'success': False, 'message': message})

    current_election = election_db.get_current_election() or {}
    election_data_json = safe_tojson(current_election)
    return render_template('verify.html',
                           election_data=current_election,
                           election_data_json=election_data_json)


if __name__ == '__main__':
    print("=" * 60)
    print("安全选举系统启动中...")
    print("=" * 60)

    current_dir = os.getcwd()
    print(f"当前工作目录: {current_dir}")

    templates_path = os.path.join(current_dir, 'templates')
    if not os.path.exists(templates_path):
        print("创建模板目录...")
        os.makedirs(templates_path)

    print("访问地址:")
    print("  http://127.0.0.1:5000/admin  - 管理页面")
    print("  http://127.0.0.1:5000/vote   - 投票页面")
    print("  http://127.0.0.1:5000/result - 结果页面")
    print("  http://127.0.0.1:5000/reveal - 结果揭示页面")
    print("  http://127.0.0.1:5000/verify - 投票验证页面")
    print("=" * 60)

    app.run(debug=True, host='0.0.0.0', port=5000)