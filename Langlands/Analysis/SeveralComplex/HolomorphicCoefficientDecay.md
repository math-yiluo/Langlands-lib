# Propagation of geometric bounds for holomorphic coefficients

Let \(g_n\) be holomorphic on the parameter disk of radius \(3\) and uniformly bounded on the closed disk of radius \(2\). Suppose that at each point of a small open disk about zero, \(\lvert g_n\rvert\) is eventually bounded by \(b^n\) for every \(b>0\). `holomorphicCoefficientDecay` gives the same eventual bounds uniformly on the closed disk of radius \(3/2\).

The proof first applies Hartogs' lemma to the functions \(c^{-n}g_n\) for an appropriate positive \(c\). A finite covering makes the resulting bound uniform on a fixed small compact disk. On the annulus from that disk to the circle of radius \(2\), apply the maximum modulus principle to \(g_n(z)/z^{kn}\). The integer \(k\) is chosen so that the factor from the outer circle offsets its radius relative to \(3/2\). The uniform bound on the small disk offsets the negative power on the inner circle. Multiplying by \(\lvert z\rvert^{kn}\) gives the desired estimate throughout the larger disk.

This is an analytic step toward continuing the normalized Rankin–Selberg integrals from a convergence chamber. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 8.1](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
