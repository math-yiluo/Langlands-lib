# Entire slice continuation from an open disk of parameters

Let \(F(z,s)\) and \(G(z,s)\) be holomorphic on the parameter disk \(\lvert z\rvert<3\) times a right and a left spectral half-plane, respectively. Suppose that for \(z\) in an open disk about zero, the two slices agree on their respective half-planes with a common entire function of \(s\). `compactParameterEntireContinuation` constructs such an entire function at \(z=1\).

Take Cauchy coefficients in the spectral variable on a circle contained in the right half-plane. Compactness gives a uniform bound for the coefficients on the closed parameter disk of radius \(2\). Wherever an entire continuation is given, the same coefficients can be computed on arbitrarily large spectral circles, so they eventually decay at every geometric rate. `holomorphicCoefficientDecay` propagates this bound uniformly to the closed parameter disk of radius \(3/2\).

The resulting Taylor series is entire in the spectral variable and holomorphic in the parameter in the disk of radius \(3/2\). It agrees with \(F\) by the Taylor formula and the identity theorem on the right half-plane. For each spectral argument on the left half-plane, the given common continuations identify the Taylor series with \(G\) near \(z=0\). The identity theorem in \(z\) gives the agreement at \(z=1\).

This derived lemma supports the inducing-parameter continuation in the adjacent-rank argument. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 8.1](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
