# Continuation of an entire reflection identity in a parameter

Suppose \(F(z,s)\) and \(G(z,s)\) are jointly holomorphic on the parameter disk \(\lvert z\rvert<3\) times a uniform right spectral half-plane. Let \(E(z,s)\) be holomorphic and nowhere zero. For each \(z\) near zero, assume entire continuations \(N_z\) and \(N_z^\vee\) agree with the two right-hand slices on a possibly smaller half-plane and satisfy \(N_z^\vee(1-s)=E(z,s)N_z(s)\). `entireSpectralReflection` gives such continuations at \(z=1\).

On the initial parameter disk, the identity theorem extends both agreements to the uniform right half-plane. Reflecting the spectral variable in \(G\) and dividing by \(E\) gives a left half-plane function. Its slices there continue from the same \(N_z\) as the right half-plane slices of \(F\). `compactParameterEntireContinuation` gives a common entire function at \(z=1\). Multiplying the reflected function by the reflected \(E\) gives the dual entire function, which agrees with \(G\) and satisfies the original reflection identity.

This is a derived analytic step for the adjacent- and equal-rank equations in inducing parameters. [Jacquet, *Archimedean Rankin–Selberg integrals*, Sections 8.1 and 9](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
