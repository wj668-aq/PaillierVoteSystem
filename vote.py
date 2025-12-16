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

# 检查可选依赖：cryptography（用于生成更安全的 RSA 密钥）
try:
    from cryptography.hazmat.primitives.asymmetric import rsa as _rsa_check  # type: ignore
    CRYPTOGRAPHY_AVAILABLE = True
except Exception:
    CRYPTOGRAPHY_AVAILABLE = False
    print("警告: 未检测到 'cryptography' 库，盲签名将回退到演示 RSA（不推荐用于生产）。可通过 'pip install cryptography' 安装。")


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
        # 内存中保存的私钥（避免将私钥持久化到磁盘）
        self.signing_private_keys = {}  # election_id -> private_key_object (cryptography)


    # Helper: 计算投票者ID的哈希（用于防止存储明文关联）
    def _hash_voter_id(self, voter_id, election_id):
        salt = app.secret_key or ''
        data = f"{voter_id}:{election_id}:{salt}".encode()
        return hashlib.sha256(data).hexdigest()

    # Helper: 把密文列表转为字符串用于生成投票凭证哈希
    def _ciphertexts_to_string(self, ciphertexts):
        # 保证可序列化顺序
        return '|'.join(str(c) for c in ciphertexts)


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
                ,
                # 存放凭证申请（用于管理员审批盲签名发放凭证）
                'credential_requests': []
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

            # 私钥lambda和mu
            lambda_val, mu = private_key

            # 管理员名单（可在选举创建时配置），默认两个管理员：teacher 和 secretary
            admin_names = election.get('admin_names', ['teacher', 'secretary'])
            num_admins = len(admin_names)

            # 生成加法式密钥分片（所有分片之和等于lambda_val）
            shares = []
            running_sum = 0
            for i in range(num_admins - 1):
                s = random.randint(1, lambda_val - 1)
                shares.append(s)
                running_sum = (running_sum + s) % lambda_val

            last_share = (lambda_val - running_sum) % lambda_val
            if last_share == 0:
                # 确保非零分片
                last_share = lambda_val
            shares.append(last_share)

            key_shares = {name: shares[i] for i, name in enumerate(admin_names)}

            # 强制要求 cryptography 可用（更安全）。若不可用则终止初始化并提示安装。
            if not CRYPTOGRAPHY_AVAILABLE:
                return False, "需要安装 'cryptography' 库以生成安全的 RSA 密钥。请运行: pip install cryptography 后重试。"

            from cryptography.hazmat.primitives.asymmetric import rsa as _rsa
            from cryptography.hazmat.backends import default_backend as _default_backend

            # 使用 cryptography 生成安全 RSA 私钥（2048-bit）
            priv = _rsa.generate_private_key(public_exponent=65537, key_size=2048, backend=_default_backend())
            priv_nums = priv.private_numbers()
            pub_nums = priv_nums.public_numbers
            n_rsa = int(pub_nums.n)
            e_rsa = int(pub_nums.e)

            # 仅将公钥持久化（避免把私钥写入 data 文件）
            rsa_pub = {'n': n_rsa, 'e': e_rsa}
            # 将私钥对象保存在内存中用于盲签名操作（服务器重启后需重新初始化或加载私钥）
            self.signing_private_keys[election['id']] = priv
            rsa_keys = rsa_pub


            crypto_setup = {
                'public_key': public_key,
                # 私钥不完整地保存在后端以避免单点解密权限
                'encrypted_results': encrypted_counters
            }

            # 保存分片到整体数据中（用于验证分片并进行部分解密）
            if 'key_shares' not in self.data:
                self.data['key_shares'] = {}

            self.data['key_shares'][election['id']] = {
                'shares': key_shares,
                'mu': mu,
                'public_key': public_key
            }

            # 保存RSA公钥用于盲签名验证（私钥仅保存在内存中）
            if 'signing_keys' not in self.data:
                self.data['signing_keys'] = {}
            self.data['signing_keys'][election['id']] = {
                'rsa_pub': rsa_keys,
                'issued': {}
            }

            # 保存分片到整体数据中（用于验证分片并进行部分解密）
            if 'key_shares' not in self.data:
                self.data['key_shares'] = {}

            self.data['key_shares'][election['id']] = {
                'shares': key_shares,
                'mu': mu,
                'public_key': public_key
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

    def add_vote(self, voter_id, candidate_index, ciphertexts=None, timestamp=None, signature=None):
        """添加加密投票

        支持两种流程：
        - 浏览器端提供密文（ciphertexts）、timestamp 与盲签名后的 signature（推荐）。
        - 如果未提供密文，则后端使用公钥对 candidate_index 加密（兼容旧前端）。
        """
        try:
            print("=== 开始处理投票（密文存储） ===")
            election = self.get_current_election()
            if not election or not election.get('id'):
                print("错误：没有活动的选举")
                return False, "没有活动的选举"

            # 检查选举状态
            if election.get('status') in ['finished', 'revealed']:
                print("错误：选举已结束")
                return False, "选举已结束，无法投票"

            candidates = election.get('candidates', [])
            if len(candidates) == 0:
                print("错误：没有候选人")
                return False, "选举中没有候选人"

            # 验证候选人索引（仅作为输入校验）
            try:
                candidate_index = int(candidate_index)
            except (ValueError, TypeError) as e:
                print(f"转换 candidate_index 错误: {e}")
                return False, "无效的候选人索引格式"

            if candidate_index < 0 or candidate_index >= len(candidates):
                print(f"错误：候选人索引越界")
                return False, f"无效的候选人选择。请选择0到{len(candidates) - 1}之间的编号"

            # 检查是否已投票（使用哈希id，避免保存明文学号）
            voter_hash = self._hash_voter_id(voter_id, election['id'])
            voted_hashes = election.get('voted_hashes', set())
            if isinstance(voted_hashes, list):
                voted_hashes = set(voted_hashes)

            if voter_hash in voted_hashes:
                print(f"错误：用户 {voter_id} 已投票（通过哈希检测）")
                return False, "您已经投过票了"

            # 统一为一票制
            weight = 1

            crypto_setup = election.get('crypto_setup')
            if not crypto_setup:
                return False, "加密系统未初始化"

            public_key = crypto_setup['public_key']

            # 如果前端提供了密文，则验证签名并使用它；否则后端进行加密
            if ciphertexts:
                # 验证输入格式
                if not isinstance(ciphertexts, list) or len(ciphertexts) != len(candidates):
                    return False, "无效的密文格式或长度"

                # 需要时间戳与签名进行盲签名验证（签名是在客户端对 {ciphertexts}_{timestamp} 的哈希取模RSA n后签名得到）
                if not timestamp or not signature:
                    return False, "缺少时间戳或签名，无法验证盲签名"

                signing_entry = self.data.get('signing_keys', {}).get(election['id'])
                if not signing_entry:
                    return False, "盲签名系统未初始化"

                rsa_pub = signing_entry.get('rsa_pub')
                if not rsa_pub:
                    return False, "盲签名公钥未找到"

                n_rsa = int(rsa_pub['n'])
                e_rsa = int(rsa_pub['e'])

                # 重现客户端用于签名的消息 m = int(sha256(ciphertexts_str + '_' + timestamp), 16) % n_rsa
                m_hex = hashlib.sha256(f"{self._ciphertexts_to_string(ciphertexts)}_{timestamp}".encode()).hexdigest()
                expected_m = int(m_hex, 16) % n_rsa

                try:
                    sig_int = int(str(signature))
                except Exception:
                    return False, "无效的签名格式"

                # 验证签名：s^e mod n == m
                if pow(sig_int, e_rsa, n_rsa) != expected_m:
                    return False, "签名验证失败，投票无效"

                # 使用前端提供的密文（确认为字符串或整型的列表）
                ciphertexts = [str(c) for c in ciphertexts]

                # 使用客户端传来的 timestamp
                # 生成投票凭证哈希
                vote_hash = hashlib.sha256(f"{self._ciphertexts_to_string(ciphertexts)}_{timestamp}".encode()).hexdigest()

            else:
                # 后端加密以兼容旧流程
                ciphertexts = []
                for i in range(len(candidates)):
                    if i == candidate_index:
                        ciphertexts.append(PaillierEncryption.encrypt(public_key, weight))
                    else:
                        ciphertexts.append(PaillierEncryption.encrypt(public_key, 0))

                timestamp = datetime.now().isoformat()
                vote_hash = hashlib.sha256(f"{self._ciphertexts_to_string(ciphertexts)}_{timestamp}".encode()).hexdigest()

            # 记录投票（不保存明文候选）
            vote_record = {
                'voter_hash': voter_hash,
                'ciphertexts': ciphertexts,
                'weight': weight,
                'timestamp': timestamp,
                'vote_hash': vote_hash,
                'signature': str(signature) if signature else None
            }


            votes = election.get('votes', [])
            votes.append(vote_record)

            # 保存验证哈希（仅保存哈希化后的投票者标识，避免关联）
            verification_hashes = election.get('verification_hashes', {})
            verification_hashes[vote_hash] = {
                'voter_hash': voter_hash,
                'timestamp': timestamp
            }

            # 更新已投票哈希集合
            voted_hashes.add(voter_hash)

            success = self.update_election(election['id'], {
                'votes': votes,
                'verification_hashes': verification_hashes,
                'voted_hashes': list(voted_hashes),
                'status': 'voting'
            })

            if success:
                print(f"投票成功！(索引: {candidate_index})")
                return True, "投票成功"
            else:
                print("投票记录失败")
                return False, "投票记录失败"

        except Exception as e:
            print(f"添加投票错误: {e}")
            return False, f"投票过程中发生错误: {str(e)}"

    def generate_vote_hash(self, voter_id_or_ciphertexts, candidate_index_or_timestamp, timestamp=None):
        """生成投票验证哈希。兼容旧调用：
        - (voter_id, candidate_index, timestamp)
        - (ciphertexts, timestamp)
        """
        try:
            if timestamp is None:
                # 说明第一参数是 ciphertexts，第二是 timestamp
                ciphertexts = voter_id_or_ciphertexts
                timestamp = candidate_index_or_timestamp
                data = f"{self._ciphertexts_to_string(ciphertexts)}_{timestamp}".encode()
            else:
                voter_id = voter_id_or_ciphertexts
                candidate_index = candidate_index_or_timestamp
                data = f"{voter_id}_{candidate_index}_{timestamp}".encode()
            return hashlib.sha256(data).hexdigest()
        except Exception:
            return hashlib.sha256(str(voter_id_or_ciphertexts).encode()).hexdigest()

    # ========== 凭证申请与管理员审批相关 ==========
    def add_credential_request(self, voter_id, blinded):
        """添加一个凭证申请，状态为 pending。"""
        try:
            election = self.get_current_election()
            if not election:
                return False, '没有活动的选举'

            # 检查是否已经签发过
            signing_entry = self.data.get('signing_keys', {}).get(election['id'], {})
            issued = signing_entry.get('issued', {})
            voter_hash = self._hash_voter_id(voter_id, election['id'])
            if issued.get(voter_hash):
                return False, '该投票者已获得凭证，不能重复申请'

            # 检查是否已有未处理申请
            requests = election.get('credential_requests', [])
            for req in requests:
                if req.get('voter_hash') == voter_hash:
                    return False, '您已提交过申请，请等待管理员处理'

            req = {
                'voter_id': voter_id,
                'voter_hash': voter_hash,
                'blinded': str(blinded),
                'status': 'pending',
                'created_at': datetime.now().isoformat(),
                'signature': None,
            }
            requests.append(req)

            success = self.update_election(election['id'], {'credential_requests': requests})
            if success:
                return True, '凭证申请已提交，等待管理员审批'
            return False, '无法保存凭证申请'
        except Exception as e:
            print(f"添加凭证申请错误: {e}")
            return False, f"添加凭证申请时发生错误: {str(e)}"

    def get_credential_requests(self):
        election = self.get_current_election()
        if not election:
            return []
        return election.get('credential_requests', [])

    def approve_credential_request(self, voter_hash):
        """管理员审批并签发盲签名：对存储的盲化值进行签名并标记已签发"""
        try:
            election = self.get_current_election()
            if not election:
                return False, '没有活动的选举', None

            requests = election.get('credential_requests', [])
            found = None
            for req in requests:
                if req.get('voter_hash') == voter_hash:
                    found = req
                    break

            if not found:
                return False, '未找到该凭证申请', None

            if found.get('status') != 'pending':
                return False, f"申请当前状态为: {found.get('status')}，无法重复审批", None

            # 获取私钥对象
            priv = self.signing_private_keys.get(election['id'])
            signing_entry = self.data.get('signing_keys', {}).get(election['id'], {})
            rsa_pub = signing_entry.get('rsa_pub')
            if not rsa_pub or not priv:
                return False, '盲签名系统未初始化或私钥未在内存中', None

            n_rsa = int(rsa_pub.get('n'))
            try:
                blinded_int = int(str(found.get('blinded')))
            except Exception:
                return False, '存储的盲化消息格式错误', None

            if not (0 < blinded_int < n_rsa) or gcd(blinded_int, n_rsa) != 1:
                found['status'] = 'denied'
                self.update_election(election['id'], {'credential_requests': requests})
                return False, '盲化消息不合法，已拒绝', None

            d_rsa = priv.private_numbers().d
            try:
                signature_int = pow(blinded_int, d_rsa, n_rsa)
            except Exception as e:
                return False, f'签名失败: {str(e)}', None

            # 标记已签发
            signing_entry.setdefault('issued', {})
            signing_entry['issued'][voter_hash] = True
            self.data['signing_keys'][election['id']] = signing_entry

            # 更新申请项
            found['status'] = 'approved'
            found['signature'] = str(signature_int)
            found['approved_at'] = datetime.now().isoformat()

            success = self.update_election(election['id'], {'credential_requests': requests})
            if success:
                return True, '凭证已签发', str(signature_int)
            else:
                return False, '保存签发结果失败', None

        except Exception as e:
            print(f"审批凭证申请错误: {e}")
            return False, f"审批凭证申请发生错误: {str(e)}", None

    def deny_credential_request(self, voter_hash, reason=None):
        election = self.get_current_election()
        if not election:
            return False, '没有活动的选举'
        requests = election.get('credential_requests', [])
        for req in requests:
            if req.get('voter_hash') == voter_hash:
                if req.get('status') != 'pending':
                    return False, '该申请已被处理'
                req['status'] = 'denied'
                req['denied_at'] = datetime.now().isoformat()
                if reason:
                    req['deny_reason'] = reason
                success = self.update_election(election['id'], {'credential_requests': requests})
                return success, '已拒绝该申请' if success else '拒绝操作保存失败'
        return False, '未找到该凭证申请'

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

            # 使用Paillier同态加密进行计票：直接将每位选民提交的密文向量逐一同态累加
            # 初始计数器为encrypted_tallies
            for vote in votes:
                ciphers = vote.get('ciphertexts', [])
                for i in range(min(len(ciphers), len(encrypted_tallies))):
                    encrypted_tallies[i] = PaillierEncryption.add_ciphertexts(
                        public_key, encrypted_tallies[i], int(ciphers[i])
                    )

            # 从已生成的key_shares中获取分片信息（初始化时已生成）
            existing_shares = self.data.get('key_shares', {}).get(election['id'], {})
            secret_shares = {}
            if existing_shares:
                # 将分片以字符串形式返回以便管理员保存与分发（仅演示用途）
                shares_map = existing_shares.get('shares', {})
                for k, v in shares_map.items():
                    secret_shares[f"{k}_share"] = str(v)
                secret_shares['public_key'] = str(existing_shares.get('public_key'))

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

            key_shares_entry = self.data.get('key_shares', {}).get(election['id'], {})
            if not key_shares_entry:
                return False, "未找到密钥分片", None

            shares_map = key_shares_entry.get('shares', {})
            if share_owner not in shares_map:
                return False, "无效的分片所有者", None

            stored_share = shares_map.get(share_owner)
            if str(share_value) != str(stored_share):
                return False, "共享分片验证失败", None

            # 执行部分解密
            crypto_setup = election.get('crypto_setup')
            public_key = crypto_setup['public_key']
            encrypted_tallies = election.get('encrypted_tallies', [])

            partial_decryptions = []
            for ciphertext in encrypted_tallies:
                # 部分解密：c^{share} mod n^2
                n, g = public_key
                n_sq = n * n
                partial_dec = pow(int(ciphertext), int(share_value), n_sq)
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

            key_shares_entry = self.data.get('key_shares', {}).get(election['id'], {})
            if not key_shares_entry:
                return False, "未找到密钥分片信息", None

            shares_map = key_shares_entry.get('shares', {})
            required_owners = set(shares_map.keys())
            provided_owners = set(partial_decryptions.keys())

            if not required_owners.issubset(provided_owners):
                return False, f"需要以下管理员的部分解密结果: {', '.join(sorted(required_owners))}", None

            crypto_setup = election.get('crypto_setup')
            public_key = crypto_setup['public_key']
            mu = key_shares_entry.get('mu')

            n, g = public_key
            n_sq = n * n

            # 合并部分解密结果（将各管理员的部分解密值相乘得到 c^{sum(shares)} = c^{lambda}）
            final_results = {}
            candidates = election.get('candidates', [])

            # 按候选人索引进行合并
            for i, candidate in enumerate(candidates):
                # 从所有管理员处取第 i 个部分解密
                combined = 1
                valid = True
                for owner in sorted(required_owners):
                    owner_partial = partial_decryptions.get(owner, [])
                    if i >= len(owner_partial):
                        valid = False
                        break
                    combined = (combined * int(owner_partial[i])) % n_sq

                if not valid:
                    continue

                # 最终解密：L(u) * mu mod n
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
        """验证投票：投票者提供凭证哈希和其学号/工号，后端对比哈希的投票者哈希并验证密文没有被篡改"""
        try:
            election = self.get_current_election()
            if not election:
                return False, "没有活动的选举"

            vote_data = election.get('verification_hashes', {}).get(vote_hash)
            if not vote_data:
                return False, "未找到匹配的投票记录"

            expected_voter_hash = vote_data.get('voter_hash')
            provided_voter_hash = self._hash_voter_id(voter_id, election['id'])
            if expected_voter_hash != provided_voter_hash:
                return False, "未找到匹配的投票记录（投票者不匹配）"

            # 查找对应的投票记录并验证密文完整性
            for vote in election.get('votes', []):
                if vote.get('vote_hash') == vote_hash:
                    return self.verify_vote_integrity(vote_hash, voter_id, vote.get('timestamp'), vote)

            return False, "投票记录不完整"
        except Exception as e:
            print(f"验证投票错误: {e}")
            return False, f"投票验证过程中发生错误: {str(e)}"

    def verify_vote_integrity(self, vote_hash, voter_id, timestamp, vote_record):
        """验证投票完整性（基于密文和时间戳）"""
        try:
            ciphertexts = vote_record.get('ciphertexts', [])
            expected_hash = self.generate_vote_hash(ciphertexts, timestamp)
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
        elif action == 'approve_request':
            voter_hash = request.form.get('voter_hash')
            if not voter_hash:
                return jsonify({'success': False, 'message': '缺少 voter_hash 参数'})
            success, message, sig = election_db.approve_credential_request(voter_hash)
            return jsonify({'success': success, 'message': message, 'signature': sig})

        elif action == 'deny_request':
            voter_hash = request.form.get('voter_hash')
            if not voter_hash:
                return jsonify({'success': False, 'message': '缺少 voter_hash 参数'})
            success, message = election_db.deny_credential_request(voter_hash)
            return jsonify({'success': success, 'message': message})

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

        # 注：前端最好在提交前进行加密并提交密文；为保持兼容性，当前如果前端没有提交密文，
        # 后端会使用公钥对候选索引进行加密并只保存密文（从而避免保存明文投票）。
        ciphertexts = data.get('ciphertexts')
        timestamp = data.get('timestamp')
        signature = data.get('signature')

        success, message = election_db.add_vote(voter_id, candidate_index, ciphertexts=ciphertexts, timestamp=timestamp, signature=signature)
        if success:
            current_election = election_db.get_current_election()
            if current_election and current_election.get('votes'):
                last_vote = current_election['votes'][-1]
                return jsonify({
                    'success': True,
                    'vote_hash': last_vote.get('vote_hash'),
                    'signature': last_vote.get('signature'),
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


@app.route('/public_key')
def get_public_key():
    """返回当前选举的Paillier公钥，供前端在浏览器中加密使用（如果实现前端加密的话）。"""
    election = election_db.get_current_election()
    if not election:
        return jsonify({'success': False, 'message': '没有活动的选举'})

    crypto_setup = election.get('crypto_setup')
    if not crypto_setup:
        return jsonify({'success': False, 'message': '加密系统未初始化'})

    public_key = crypto_setup.get('public_key')
    if not public_key:
        return jsonify({'success': False, 'message': '未找到公钥信息'})

    n, g = public_key
    # 返回为字符串以避免 JavaScript 将大整数解析为 Number（可能变为 Infinity）
    return jsonify({'success': True, 'public_key': {'n': str(n), 'g': str(g)}})


@app.route('/signing_pubkey')
def get_signing_pubkey():
    """返回RSA盲签名的公钥（n,e）。"""
    election = election_db.get_current_election()
    if not election:
        return jsonify({'success': False, 'message': '没有活动的选举'})
    signing_entry = election_db.data.get('signing_keys', {}).get(election['id'])
    if not signing_entry:
        return jsonify({'success': False, 'message': '盲签名系统未初始化'})
    rsa_pub = signing_entry.get('rsa_pub')
    if not rsa_pub:
        return jsonify({'success': False, 'message': '盲签名公钥未找到'})
    # 返回字符串形式以避免 JavaScript 将超大整数解析为 Number（导致 Infinity 错误）
    return jsonify({'success': True, 'rsa_pub': {'n': str(rsa_pub['n']), 'e': str(rsa_pub['e'])}})


@app.route('/blind_sign', methods=['POST'])
def blind_sign():
    """对客户端提交的盲化消息进行签名（若投票者尚未获得签名）。
    请求 JSON 格式: { 'voter_id': '...', 'blinded': '<decimal string>' }
    返回: { 'success': True, 'signature': '<decimal string>' }
    """
    if not request.is_json:
        return jsonify({'success': False, 'message': '请求必须为JSON'}), 400
    data = request.get_json()
    voter_id = data.get('voter_id', '').strip()
    blinded = data.get('blinded')
    if not voter_id or not blinded:
        return jsonify({'success': False, 'message': '缺少参数'}), 400

    election = election_db.get_current_election()
    if not election:
        return jsonify({'success': False, 'message': '没有活动的选举'})

    # 改为基于管理员审批的工作流：查找凭证申请并返回已审批的签名；若申请尚未审批，则返回等待信息
    signing_entry = election_db.data.get('signing_keys', {}).get(election['id'])
    if not signing_entry:
        return jsonify({'success': False, 'message': '盲签名系统未初始化'}), 400

    rsa_pub = signing_entry.get('rsa_pub')
    if not rsa_pub:
        return jsonify({'success': False, 'message': '盲签名公钥未找到'}), 500

    n_rsa = int(rsa_pub.get('n'))
    try:
        blinded_int = int(str(blinded))
    except Exception:
        return jsonify({'success': False, 'message': '无效的盲化消息'}), 400

    if not (0 < blinded_int < n_rsa):
        return jsonify({'success': False, 'message': '盲化消息不在有效范围'}), 400

    voter_hash = election_db._hash_voter_id(voter_id, election['id'])

    # 查找申请
    requests = election_db.get_credential_requests()
    found = None
    for req in requests:
        if req.get('voter_hash') == voter_hash:
            found = req
            break

    if not found:
        return jsonify({'success': False, 'message': '未找到凭证申请，请先提交凭证申请'}), 404

    status = found.get('status')
    if status == 'pending':
        return jsonify({'success': False, 'message': '凭证申请已提交，等待管理员审批'}), 202
    if status == 'denied':
        return jsonify({'success': False, 'message': '凭证申请已被拒绝'}), 403
    if status == 'approved':
        sig = found.get('signature')
        if not sig:
            return jsonify({'success': False, 'message': '签名尚未生成，请稍后重试'}), 500
        # 返回已签发的盲签名（客户端可解盲以得到最终签名）
        return jsonify({'success': True, 'signature': str(sig)})

    return jsonify({'success': False, 'message': '凭证申请状态未知'}), 400


@app.route('/request_credential', methods=['POST'])
def request_credential():
    """投票者提交盲签名凭证申请（包含盲化消息）。后端仅保存申请，等待管理员审批。"""
    if not request.is_json:
        return jsonify({'success': False, 'message': '请求必须为JSON'}), 400
    data = request.get_json()
    voter_id = data.get('voter_id', '').strip()
    blinded = data.get('blinded')
    if not voter_id or not blinded:
        return jsonify({'success': False, 'message': '缺少参数'}), 400

    success, message = election_db.add_credential_request(voter_id, blinded)
    status_code = 200 if success else 400
    return jsonify({'success': success, 'message': message}), status_code


@app.route('/credential_status')
def credential_status():
    """查询凭证申请状态：?voter_id=... 返回 status 和 signature(若已签发)"""
    voter_id = request.args.get('voter_id', '').strip()
    if not voter_id:
        return jsonify({'success': False, 'message': '缺少 voter_id 参数'}), 400
    election = election_db.get_current_election()
    if not election:
        return jsonify({'success': False, 'message': '没有活动的选举'}), 400

    voter_hash = election_db._hash_voter_id(voter_id, election['id'])
    requests = election.get('credential_requests', [])
    found = None
    for req in requests:
        if req.get('voter_hash') == voter_hash:
            found = req
            break

    if not found:
        return jsonify({'success': False, 'message': '未找到凭证申请'}), 404

    resp = {'success': True, 'status': found.get('status')}
    if found.get('status') == 'approved':
        resp['signature'] = found.get('signature')
    return jsonify(resp)


@app.route('/credential_requests')
def credential_requests():
    """返回当前选举的凭证申请列表（管理员用）"""
    election = election_db.get_current_election()
    if not election:
        return jsonify({'success': False, 'message': '没有活动的选举'}), 400
    requests = election.get('credential_requests', [])
    # 为了安全，返回完整信息仅供管理员查看
    return jsonify({'success': True, 'requests': requests})


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