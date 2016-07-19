#!/usr/bin/python
# -*- coding: utf-8 -*-

import copy

def gcd(a, b):
    """
    Return the greatest common denominator of integers a and b.
    gmpy2.gcd(a, b)
    """
    while b:
        a, b = b, a % b
    return a

def lcm(a, b):
    return a * b / (gcd(a, b))

def egcd(a, b):
    """
    ax + by = 1
    ax ≡ 1 mod b
    Return a 3-element tuple (g, x, y), the g  = gcd(a, b)
    gmpy2.gcdext(a, b)
    """    
    if a == 0:
        return (b, 0, 1)
    else:
        g, y, x = egcd(b % a, a)
        return (g, x - (b // a) * y, y)

def mod_inv(a, m):
    """
    ax ≡ 1 mod m
    gmpy2.invert(a, m)
    """
    g, x, y = egcd(a, m)
    assert g == 1
    return x % m

def int2mem(x):
    """
    0x12233 => '\x33\x22\x01'
    """
    pad_even = lambda x : ('', '0')[len(x)%2] + x
    x = list(pad_even(format(x, 'x')).decode('hex'))
    x.reverse()
    return ''.join(x)

def mem2int(x):
    """
    '\x33\x22\x01' => 0x12233
    """
    x = list(x)
    x.reverse()
    return int(''.join(x).encode('hex'), 16)

###########################################################
# class
###########################################################
class GaussMatrix:
    """
    A*X ≡ B (mod p),p为大于0的整数。

    高斯消元求解模线性方程组。先化简为上三角，然后回代求解。
    当r(A) <= n时，一定有多解；
    当r(A) == n时，有多解或唯一解；
    当r(A) != r(A~)时，无解。
    r(A)为系数矩阵的秩，r(A)为增广矩阵的秩，n为未知数的个数。

    http://www.docin.com/p-1063811671.html讨论了gcd(|A|, m) = 1时的LU分解解法，
    本文包括了gcd(|A|, m) > 1时的解法，

    化简原则：
        1、系数与模互质
        2、系数加某一行n次后，对应的系数与模的GCD最小
        3、将1或2得到的系数移到对角线上

    初始化参数：
        matrix：方程组的增广矩阵（最后一列为常数项）。
            matrix = [
                [ 69,  75,  78,  36,  58],
                [ 46,  68,  51,  26,  42],
                [ 76,  40,  42,  49,  11],
                [ 11,  45,   2,  45,   1],
                [ 15,  67,  60,  14,  72],
                [ 76,  67,  73,  56,  58],
                [ 67,  15,  68,  54,  75],
            ]    
        mod：模数

    函数：
        gauss()：求解方程

    输出变量：
        error_str：出错的信息
        count：解的数量
    """
    def __init__(self, matrix, mod):
        self.matrix = copy.deepcopy(matrix)
        self.d = None

        self.r = len(matrix)
        self.c = len(matrix[0])
        self.N = len(matrix[0]) - 1
        self.mod = mod
        self.count = 1
        self.error_str = "unknown error"

    def verify_solution(self, solution):
        for d in self.matrix:
            result = 0
            for r in map(lambda x,y:0 if None == y else x*y, d, solution):
                result += r
            if (result % self.mod) != ((d[-1]) % self.mod):
                return 0
        return 1
        
    def swap_row(self, ra, rb):
        (self.d[ra], self.d[rb]) = (self.d[rb], self.d[ra])

    def swap_col(self, ca, cb):
        for j in range(self.r):
            (self.d[j][ca], self.d[j][cb]) = (self.d[j][cb], self.d[j][ca])

    def inv_result(self, r, n):
        """
        求解第n个未知数，r已经获得的解。形如：[None,None, ..., n+1, ...]

        a*x ≡ b(mod m)
        x有解的条件：gcd(a,m) | b。也即a,m互质时一定有解，不互质时，b整除gcd(a,m)也有解，否则无解。
        解的格式为：x0+k(m/gcd(a,m))，其中x0为最小整数特解，k为任意整数。
        返回[x0, x1, ...xn]，其中x0 < x1 < xn < m。
        """
        b = self.d[n][self.N]
        a = self.d[n][n]
        m = self.mod
        k = gcd(a, m)            
        for j in xrange(n + 1, self.N):
            b = (b - (self.d[n][j] * r[j] % m)) % m

        if 1 == k:
            return [mod_inv(a, m) * b % m]
        else:
            if k == gcd(k, b):
                a /= k
                b /= k
                m /= k

                x0 = mod_inv(a, m) * b % m
                x = []
                for i in xrange(k):
                    x.append(x0 + m*i)
                return x
        return None

    def find_min_gcd_row_col(self, i, j):
        # 查找直接互质的对角线系数
        for k in xrange(i, self.r):
            for l in xrange(j, self.c - 1):
                if(1 == gcd(self.d[k][l], self.mod)):
                    return [k, l]


        def add_min_gcd(a, b, m):
            r = [m, 1]
            g = gcd(a, b)
            if g:
                i = a / g
                for j in xrange(i):
                    g = gcd((a + j * b) % m, m)
                    if g < r[0]:
                        r[0] = g
                        r[1] = j
                    if g == 1:
                        break
            return r

        # 查找加乘后GCD最小的对角线系数
        #   [加乘后的最大公约数,加乘的倍数,要化简的行号,加乘的行号,要化简的列号]
        r = [self.mod, 1, i, i + 1, j]
        for k in xrange(i, self.r):
            for kk in xrange(k+1, self.r):
                for l in range(j, self.c - 1):
                    rr = add_min_gcd(self.d[k][l], self.d[kk][l], self.mod)
                    if rr[0] < r[0]:
                        r[0] = rr[0]
                        r[1] = rr[1]
                        r[2] = k
                        r[3] = kk
                        r[4] = l
                        pass
                    if(1 == rr[0]):
                        break
        g = r[0]
        n = r[1]
        k = r[2]
        kk = r[3]
        l = r[4]

        if n and g < self.mod:
            self.d[k] = map(lambda x, y : (x + n*y)%self.mod, self.d[k], self.d[kk])
        return [k, l]
        
    def mul_row(self, i, k, j):
        a = self.d[k][j]
        b = self.d[i][j]

        def get_mul(a, b, m):
            k = gcd(a, m)
            if 1 == k:
                return mod_inv(a, m) * b % m
            else:
                if k == gcd(k, b):
                    return mod_inv(a/k, m/k) * (b/k) % (m/k)
            return None

        if b:
            mul = get_mul(a, b, self.mod)
            if None == mul:
                print_matrix(self.d)
                assert(mul != None)
            self.d[i] = map(lambda x, y : (y - x*mul) % self.mod, self.d[k], self.d[i])


    def gauss(self):
        """
        返回解向量，唯一解、多解或无解(None)。
        例如：[[61, 25, 116, 164], [61, 60, 116, 94], [61, 95, 116, 24], [61, 130, 116, 129], [61, 165, 116, 59]]
        """

        self.d = copy.deepcopy(self.matrix)
        for i in xrange(self.r):
            for j in xrange(self.c):
                self.d[i][j] = self.matrix[i][j] % self.mod #把负系数变成正系数

        if self.r < self.N:
            self.d.extend([[0]*self.c]*(self.N - self.r))          

        # 化简上三角
        index = [x for x in xrange(self.N)]
        for i in range(self.N):
            tmp = self.find_min_gcd_row_col(i, i)
            if(tmp):
                self.swap_row(i, tmp[0])
                (index[i], index[tmp[1]]) = (index[tmp[1]], index[i])
                self.swap_col(i, tmp[1])
            else:
                self.error_str = "no min"
                return None

            for k in range(i + 1, self.r):
                self.mul_row(k, i, i)

        # print_matrix(self.d)
        if self.r > self.N:
            for i in xrange(self.N, self.r):
                for j in xrange(self.c):
                    if self.d[i][j]:
                        self.error_str = "r(A) != r(A~)"
                        return None

        # 判断解的数量
        for i in xrange(self.N):
            self.count *= gcd(self.d[i][i], self.mod)

        if self.count > 100:
            self.error_str = "solution too more:%d" % (self.count)
            return None            

        # 回代
        result = [[None]*self.N]
        for i in range(self.N - 1, -1, -1):
            new_result = []
            for r in result:
                ret = self.inv_result(r, i)
                if ret:
                    for rr in ret:
                        l = r[:]
                        l[i] = rr
                        new_result.append(l)

                else:
                    self.error_str = "no inv:i=%d" % (i)
                    return None

            result = new_result

        # 调整列变换导致的未知数顺序变化
        for i in xrange(len(result)) :
            def xchg(a, b):
                result[i][b] = a
            map(xchg, result[i][:], index)

        return result

###########################################################
# test
###########################################################
def print_array(x):
    prn = "\t["
    for j in x:
        if j:
            prn += "%3d, " % j
        else:
            prn += "  0, "

    print prn[:-2]+"],"

def print_matrix(x):
    print "["    
    for i in x:
        print_array(i)
    print "]"

def random_test(times):
    import random
    for i in xrange(times):
        print "\n============== random test %d ==============\n" % i        
        mod = random.randint(5, 999)
        col = random.randint(2, 30)        
        row = random.randint(2, 30)

        solution = map(lambda x : random.randint(0, mod - 1), [xc for xc in xrange(col)])

        matrix = []
        for y in xrange(row):
            array = map(lambda x : random.randint(0, mod), [xc for xc in xrange(col)])

            t = 0
            for j in map(lambda x,y:0 if None == y else x*y, array, solution):
                t += j
            array.append(t % mod)

            matrix.append(array)

        run_test(mod, solution, matrix)

def static_test_ex():
    mod = 37
    solution = [6, 10, 5, 11, 32, 39, 6, 42, 7, 18, 21, 8, 8, 27]
    matrix = [
        [ 32,  43,  11,  27,  14,  41,  27,  20,   0,  37,   7,  12,   9,  16,  12],
        [ 23,  35,  31,  25,  46,  27,  48,   0,   4,  19,  43,  11,  31,  24,  36],
        [ 48,  10,  47,   1,  42,  26,   0,  21,  10,  23,   7,   5,  13,  32,  41],
        [ 15,   0,   6,  24,   6,  36,   4,  36,  18,  46,  33,  20,   4,  20,  39],
        [  4,  37,   3,  39,  26,  33,  13,  32,  23,  11,  45,  45,  29,  32,  35],
        [ 38,   8,  38,  47,   1,  34,  36,  46,  47,   0,  22,  23,  21,  31,  21],
        [ 21,   3,  17,  15,  46,  42,   7,  17,  12,  37,  30,   3,  14,  12,  16],
        [  7,  22,  14,  31,  31,  19,  34,  46,   9,  33,  12,  18,   4,  15,  32],
        [ 13,  41,  35,  25,  19,   9,  44,   8,   0,  42,  15,  20,   3,  47,  29],
        [ 36,  21,  36,  13,  37,  40,  21,  39,   2,  16,  26,   4,  15,   2,  23],
        [ 41,  19,  28,   2,  42,  24,  27,  21,  21,  35,   3,  18,   7,  22,  36],
        [ 42,  34,  17,  40,  26,   7,  14,   0,   7,  46,  30,  14,  34,  22,  39],
        [ 18,   1,  40,  38,  17,  45,  24,  34,  34,   9,  32,  24,   9,   2,  45],
        [ 43,   2,   1,  29,  47,  48,  28,  37,  10,  23,  35,  34,  37,  44,  35],
    ]

    run_test(mod, solution, matrix)

def static_test():
    mod = 26
    solution = [23,15,19,13,25,17,24,18,11]
    matrix = [
        [11,12,7,0,0,0,0,0,0],
        [0,0,0,11,12,7,0,0,0],
        [0,0,0,0,0,0,11,12,7],
        [14,18,23,0,0,0,0,0,0],
        [0,0,0,14,18,23,0,0,0],
        [0,0,0,0,0,0,14,18,23],
        [17,5,19,0,0,0,0,0,0],
        [0,0,0,17,5,19,0,0,0],
        [0,0,0,0,0,0,17,5,19],
    ]  

    for i in xrange(len(matrix)):
        t = 0
        for j in map(lambda x,y:0 if None == y else x*y, matrix[i], solution):
            t += j
        matrix[i].append(t % mod)

    run_test(mod, solution, matrix)

def run_test(mod, solution, matrix):
    print "row = %d, col = %d" % (len(matrix), len(matrix[0])-1)
    print "mod = %d" % (mod)
    print "solution =", solution

    print "matrix ="
    print_matrix(matrix)

    g = GaussMatrix(matrix, mod)

    ret = g.gauss()
    if not ret:
        print "error:"
        print_matrix(g.d)
        print "error_str:", g.error_str
    else:
        print "times:", len(ret), g.count
        print "result:"
        for x in ret:
            print x


def DSA_comK():
    """
    # DSA两次签名使用相同的随机数k可导致私钥x泄漏
    # p：L bits长的素数。L是64的倍数，范围是512到1024；
    # q：p - 1的160bits的素因子；
    # g：g = h^((p-1)/q) mod p，h满足h < p - 1, h^((p-1)/q) mod p > 1；
    # x：x < q，x为私钥 ；    
    # y：y = g^x mod p ，( p, q, g, y )为公钥；

    # r = ( g^k mod p ) mod q
    # s = ( k^(-1) (HASH(m) + xr)) mod q
    # 签名结果是( m, r, s )
    """
    import hashlib
    p = 0x8c286991e30fd5341b7832ce9fe869c0a73cf79303c2959ab677d980237abf7ecf853015c9a086c4330252043525a4fa60c64397421caa290225d6bc6ec6b122cd1da4bba1b13f51daca8b210156a28a0c3dbf17a7826f738fdfa87b22d7df990908c13dbd0a1709bbbab5f816ddba6c8166ef5696414538f6780fdce987552b
    g = 0x49874582cd9af51d6f554c8fae68588c383272c357878d7f4079c6edcda3bcbf1f2cbada3f7d541a5b1ae7f046199f8f51d72db60a2601bd3375a3b48d7a3c9a0c0e4e8a0680f7fb98a8610f042e10340d2453d3c811088e48c5d6dd834eaa5509daeb430bcd9de8aabc239d698a655004e3f0a2ee456ffe9331c5f32c66f90d

    q = 0x843437e860962d85d17d6ee4dd2c43bc4aec07a5
    m1 = 0x3132333435363738
    r1 = 0x4d91a491d95e4eef4196a583cd282ca0e625f36d
    s1 = 0x3639b47678abf7545397fc9a1af108537fd1dfac

    m2 = 0x49276c6c206265206261636b2e
    r2 = 0x4d91a491d95e4eef4196a583cd282ca0e625f36d
    s2 = 0x314c044409a94f4961340212b42ade005fb27b0a

    # M1 = mem2int(hashlib.sha1(int2mem(m1)).digest())
    M1 = int(hashlib.sha1('3132333435363738'.decode('hex')).hexdigest(), 16)
    # M2 = mem2int(hashlib.sha1(int2mem(m2)).digest())
    M2 = int(hashlib.sha1('49276c6c206265206261636b2e'.decode("hex")).hexdigest(), 16)

    matrix_c = [
        [0x3639b47678abf7545397fc9a1af108537fd1dfac, -0x4d91a491d95e4eef4196a583cd282ca0e625f36d, M1],
        [0x314c044409a94f4961340212b42ade005fb27b0a, -0x4d91a491d95e4eef4196a583cd282ca0e625f36d, M2]
    ]

    print "mod = %d" % (q)
    print "matrix ="
    print_matrix(matrix_c)

    Gauss = GaussMatrix(matrix_c, q)

    ret = Gauss.gauss()
    if not ret:
        print "error:"
        print_matrix(Gauss.d)
        print "error_str:", Gauss.error_str
    else:
        k = ret[0][0]
        x = ret[0][1]
        print "k: %x" % (k)
        print "x: %x" % (x)
        print Gauss.verify_solution(ret[0])


if __name__ == "__main__":
    # DSA_comK()

    static_test()
    # static_test_ex()
    # random_test(1)
    exit(0)
