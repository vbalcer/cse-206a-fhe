load "test_c.spyx"

class EncryptionSystem:
	def __init__(self, n, q, beta, full=True):
		self.n = n
		self.ring = Integers(q)
		self.beta = beta
		self.full = full
		self.l = ceil(q.log(2))
		
		if full:
			self.m = n*self.l
			self.G = block_matrix([[2^(i)*identity_matrix(self.ring, n)] for i in range(self.l)])
		else:
			self.m = 1
			self.G = zero_matrix(self.ring, 1, n)
			self.G[0,n-1] = round(q/2)
	
	def keyGen(self):
		return random_vector(self.ring, self.n - 1)
	
	def encrypt(self, m, s):
		A = random_matrix(self.ring, self.m, self.n - 1)
		e = vector(self.ring, random_vector(self.m, -self.beta, self.beta + 1))
		return block_matrix(self.ring, [[A, matrix(self.ring, (A*s + e)).transpose()]]) + m*self.G
	
	def __round(self, v):
		q = self.ring.order()
		v1 = ZZ(v) if v <= round(q/2) else ZZ(v) - q
		return 0 if abs(v1) <= q/4 else 1
	
	def decrypt(self, c, s):
		sbar = vector(self.ring, list(-s) + [1])
		return self.__round(c[self.m - 1]*sbar)
	
	def hAdd(self, c1, c2):
		return c1 + c2
	
	def hLstAdd(self, ci, cj):
		c = []
		q = len(ci)
		
		# instead of calling hMul in the loop, we decompose the
		# first vector entirely and use normal multiplication. this
		# allows to cut down on the number of decompositions
		ci_dec = [self.decomposeMat(cc) for cc in ci]
		
		for k in range(q):
			ck = ci_dec[0]*cj[k]
			for t in range(1, q):
				ck = self.hAdd(ck, ci_dec[t]*cj[(k-t)%q])
			c.append(ck)
		return c
	
	def decomposeMat(self, c1):
		return decompose(c1, self.l, self.ring)
	
	def hMul(self, c1, c2):
		if not self.full:
			raise RuntimeError("Homomorphic multiplication only works for the full system!")
		return self.decomposeMat(c1)*c2
	
	def publicDecryptionKey(self, Ebig, z, s):
		q = self.ring.order()
		pubS = {}
		for i,j in [(i,j) for i in range(self.n - 1) for j in range(self.l)]:
			si = s[i]*(2^j)
			e = zero_vector(q)
			e[ZZ(si)] = 1
			pubS[(i,j)] = map(lambda m: Ebig.encrypt(m, z), e)
		return pubS
	
	def hDecrypt(self, pubS, c, Ebig):
		vs = []
		for i in range(self.n - 1):
			ci = self.decomposeMat([c[0, i]])[0]
			for j in range(len(ci)):
				if ci[j] == 1:
					vs.append(pubS[i,j])
		v = reduce(lambda x, y: Ebig.hLstAdd(x, y), vs[1:], vs[0])
		v.reverse()
		v = v[-ZZ(c[0][-1]):] + v[:-ZZ(c[0][-1])]
		
		return reduce(lambda x, y: Ebig.hAdd(x, y), v[q/4+1:3*q/4], v[q/4])
	
	def publicKeySwitchingKey(self, E, z, s):
		q1 = E.ring.order()
		q = self.ring.order()
		g = RR(q1)/RR(q)*vector(RR, map(lambda x: 2^x, range(self.l)))
		sis = map(lambda x: vector(E.ring, map(lambda x: self.ring(round(x)), RR(x)*g)), s)
		K = []
		for si in sis:
			Ai = random_matrix(E.ring, self.l, E.n-1)
			ei = vector(E.ring, random_vector(self.l, -self.beta, self.beta + 1))
			K.append(block_matrix(E.ring, [[Ai, (Ai*z + ei +si).column()]]))
		return K
	
	def switchKeys(self, c, K, Ebig):
		cis = [Ebig.decomposeMat([ci]) for ci in c[:-1]]
		v = -1*sum(ci*Ki for ci, Ki in zip(cis, K))
		q1 = Ebig.ring.order()
		q = self.ring.order()
		v[0, -1] = v[0, -1] + self.ring(round(RR(q)/RR(q1)*RR(c[-1])))
		return v
	
	def estimateHMuls(self):
		q = self.ring.order()
		return (self.n*self.l*q)/2
	
	def hNot(self, c):
		return self.G - c
	
	def hNand(self, c1, c2, Ebig, pubS, K):
		c1prime = self.hDecrypt(pubS, c1, Ebig)
		c2prime = self.hDecrypt(pubS, c2, Ebig)
		cprime = Ebig.hMul(c1prime, c2prime)
		c = self.switchKeys(cprime[-1], K, Ebig)
		return self.hNot(c)
	
def testSystem(N = 20, full=True):
	for i in xrange(100):
		E = EncryptionSystem(16, 4096, 4, full)
		s = E.keyGen()
		m1 = randint(0,1)
		c = E.encrypt(m1, s)
		m = E.decrypt(c,s)
		if (m != m1):
			return False
	return True

def checkKeySwitching(n, q, beta, N, Q, Beta, T=20):
	for i in range(T):
		E = EncryptionSystem(n, q, beta, False)
		s = E.keyGen()
		Ebig = EncryptionSystem(N, Q, Beta, True)
		z = Ebig.keyGen()
		
		K = Ebig.publicKeySwitchingKey(E, s, z)
		m = randint(0,1)
		c = Ebig.encrypt(m, z)
		c1 = E.switchKeys(c[-1], K, Ebig)
		m1 = E.decrypt(c1, s)
		
		if m != m1:
			return False
	return True

def checkHDecryption(n, q, beta, N, Q, Beta, T=20):
	for i in range(T):
		E = EncryptionSystem(n, q, beta, False)
		s = E.keyGen()
		Ebig = EncryptionSystem(N, Q, Beta, True)
		z = Ebig.keyGen()
		
		pubS = E.publicDecryptionKey(Ebig, z, s)
		m = randint(0,1)
		c = E.encrypt(m, s)
		c1 = E.hDecrypt(pubS, c, Ebig)
		m1 = Ebig.decrypt(c1, z)
		
		if m != m1:
			return False
	return True

def checkNand(n, q, beta, N, Q, Beta, T=20):
	for i in range(T):
		print i
		E = EncryptionSystem(n, q, beta, False)
		s = E.keyGen()
		Ebig = EncryptionSystem(N, Q, Beta, True)
		z = Ebig.keyGen()
		
		pubS = E.publicDecryptionKey(Ebig, z, s)
		K = Ebig.publicKeySwitchingKey(E, s, z)
		
		m1 = randint(0,1)
		m2 = randint(0,1)
		c1 = E.encrypt(m1, s)
		c2 = E.encrypt(m2, s)
		
		c = E.hNand(c1, c2, Ebig, pubS, K)
		if (not(m1*m2)) != E.decrypt(c, s):
			return False
		
	return True

print "checking nontrivial nand gate"
l = 6
n = 4
q = 2^l
beta = 1
N = 4
Q = 2^25
Beta = 1
#~ print checkKeySwitching(n, q, beta, N, Q, Beta)
#~ print checkHDecryption(n, q, beta, N, Q, Beta)
#~ print checkNand(n, q, beta, N, Q, Beta)

E = EncryptionSystem(n, q, beta, False)
s = E.keyGen()
Ebig = EncryptionSystem(N, Q, Beta, True)
z = Ebig.keyGen()

print "decompositions: ", n*l*q
c = Ebig.encrypt(randint(0,1), z)
timeit("Ebig.decomposeMat(c)")

print "matrix multiplications: ", n*l*q^2
c = Ebig.encrypt(randint(0,1), z)
c_dec = Ebig.decomposeMat(c)
timeit("c_dec*c")


#~ print "search for smallest Q s.t. homomorphic decryption works for beta=1:"
#~ beta = 1
#~ for ne in range(2, 8):
	#~ n = 2^ne
	#~ for l in range(3, 8):
		#~ q = 2^l
		#~ Q = q
		#~ while not checkHDecryption(n,q,beta,n,Q,beta, 10):
			#~ Q *= 2
		#~ print "n={0}, q={1}, Q={2}".format(n,q,Q)

#~ print "search for largest Q s.t. key switching works for beta=1:"
#~ beta = 1
#~ for ne in range(2, 8):
	#~ n = 2^ne
	#~ for l in range(3, 11):
		#~ q = 2^l
		#~ Q = q
		#~ while checkKeySwitching(n,q,beta,n,Q,beta):
			#~ Q *= 2
		#~ print "n={0}, q={1}, Q={2}".format(n,q,Q)

