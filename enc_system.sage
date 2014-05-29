class EncryptionSystem:
	def __init__(self, n, q, beta, full=True):
		self.n = n
		self.ring = Integers(q)
		self.beta = beta
		self.full = full
		if full:
			l = ceil(q.log(2))
			self.m = n*l
			self.G = block_matrix([[2^(i)*identity_matrix(self.ring, n)] for i in range(l)])
		else:
			self.m = 1
			self.G = zero_matrix(self.ring, 1, n)
			self.G[0,n-1] = round(q/2)
	
	def keyGen(self):
		return random_vector(self.ring, self.n - 1)
	
	def encrypt(self, m, s):
		A = random_matrix(self.ring, self.m, self.n - 1)
		e = vector(self.ring, random_vector(self.m, -self.beta, self.beta))
		return block_matrix([[A, matrix(self.ring, (A*s + e)).transpose()]]) + m*self.G
	
	def __round(self, v):
		q = self.ring.order()
		v1 = ZZ(v) if v <= round(q/2) else ZZ(v) - q
		return 0 if abs(v1) <= q/4 else 1
	
	def decrypt(self, c, s):
		sbar = vector(self.ring, list(-s) + [1])
		return self.__round(c[self.m - 1]*sbar)
	
	def hAdd(self, c1, c2):
		return c1 + c2
	
	def __decomposeMat(self, c1):
		l = self.m/self.n
		C1i = []
		C1 = matrix(ZZ, c1)
		for i in range(l):
			Ci = matrix(ZZ, matrix(Integers(2), C1))
			C1i.append(Ci)
			C1 = (1/2)*(C1 - Ci)
		return block_matrix(self.ring, [C1i])

	def hMul(self, c1, c2):
		if not self.full:
			raise RuntimeError("Homomorphic multiplication only works for the full system!")
		return self.__decomposeMat(c1)*c2

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
	

E = EncryptionSystem(16, 4096, 4)
s = E.keyGen()
m1 = randint(0,1)
m2 = randint(0,1)
c1 = E.encrypt(m1, s)
c2 = E.encrypt(m2, s)
m = E.decrypt(E.hMul(c1, c2), s)
