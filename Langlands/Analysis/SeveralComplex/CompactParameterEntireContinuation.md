# Entire slice continuation from an open disk of parameters

Let \(F(z,s)\) be holomorphic on the parameter disk \(\lvert z\rvert<3\) times a right spectral half-plane. If \(F(z,\cdot)\) extends to an entire function of \(s\) for every \(z\) in an open disk about zero, `compactParameterJointEntireContinuation` gives a joint holomorphic extension to \(\lvert z\rvert<3/2\) times \(\mathbb C\).

Take Cauchy coefficients in the spectral variable on a circle contained in the right half-plane. Compactness gives a uniform bound for the coefficients on the closed parameter disk of radius \(2\). Wherever an entire continuation is given, the same coefficients can be computed on arbitrarily large spectral circles, so they eventually decay at every geometric rate. `holomorphicCoefficientDecay` propagates this bound uniformly to the closed parameter disk of radius \(3/2\).

The resulting Taylor series is entire in the spectral variable and holomorphic in the parameter on the disk of radius \(3/2\). Hartogs's theorem gives joint holomorphy. The Taylor formula and the identity theorem give agreement with \(F\) on the right half-plane.

`compactParameterEntireContinuation` also treats a function \(G(z,s)\) holomorphic on \(\lvert z\rvert<3\) times a left spectral half-plane. Suppose the given entire functions near \(z=0\) also agree with the slices of \(G\) on that half-plane. For each left half-plane spectral argument the identity theorem in the parameter then identifies the joint continuation with \(G\) throughout \(\lvert z\rvert<3/2\). The slice at \(z=1\) gives the common entire extension.

These derived lemmas support the inducing-parameter continuation in the adjacent-rank argument. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 8.1](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
