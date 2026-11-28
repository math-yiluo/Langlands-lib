# Equality of the finite projection and original Levi pairings

Fix a standard parabolic \(P=MU\), the central split torus data and
right-invariant norm-one Haar, a positive-size closed ambient matrix
embedding, and an Iwasawa compact. Suppose the Levi pairings of a
continuous parabolic-quotient function \(\varphi\) of height growth
have the finite expansion of `leviFibrePairingExpansionIntegrand`.
The kernels in the finite expansion are adelic test functions.
`leviPairing_finiteLeviFibreProjection_eq_of_fibreExpansion` proves
equality with the pairings of `finiteLeviFibreProjection` for every
continuous rationally invariant, cuspidal test with weighted
norm-one representatives. The kernel test-function and uniform
partial-convolution rapid-decay propositions are inputs.

For a given test \(t\), the weighted bound at degree zero makes its
norm-one restriction bounded. This gives a class \(v_t\) in cuspidal
\(L^2\). The majorants for smoothing permit exchanging the positive
and norm-one quotient integrals. At a fixed positive point \(b\), the
quotient transposition moves the kernel to \(v_t\). Its partial
convolution \(s\) is continuous, rationally invariant and cuspidal.
The uniform decay estimate gives weighted norm-one representatives
for \(s\), so \(s\) also defines a cuspidal class \(v_s\). The paired
norm-one and positive quotient measures identify the transposed
integral with the inner product of \(v_s\) and the vector of the
projection at \(b\), times the inverse modulus.

In that inner product the Bochner vector formula is the recentered
finite expansion for the pairing of \(\varphi\) with \(s\) at the
translated base point \(\iota(p(b))k_j\). The kernel-vector unfolding
allows the continuous and Hilbert test to be used at the same
argument. Reversing the recentering and using the supplied expansion
gives the original pairing at that base point. Centrality of \(p(b)\)
identifies its integrand with the matching summand of the original
pairing against \(t\). Integrability of the finitely many smoothed
pairing integrands lets the sum pass through the integral.

This is the identity of norm-one pairings in Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, §6.2,
equation (6.8), implemented using the parabolic Iwasawa formula and
cuspidal smoothing in Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series*, I.1.13 and I.3.4.
