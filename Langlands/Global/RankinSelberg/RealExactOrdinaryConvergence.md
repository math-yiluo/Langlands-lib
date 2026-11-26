# Half-plane convergence for exact real ordinary tests

`RealExactOrdinaryConvergenceStatement` uses the Whittaker models of
`realOrdinaryUnequalTest` and `realOrdinaryEqualTest`, with opposite
nonzero real additive parameters and the supplied compatible quotient
measure. For each test it gives a common right half-plane on which the
ordinary and dual kernels are integrable and both integral functions are
holomorphic. In equal rank, the dual test uses the Fourier transform
with parameter \(-a\). In unequal rank the dual kernel includes the
rectangular variable with the measure for \(a\).

The proof combines `realExactWhittakerDerivativeGrowth` with
`realLocalWhittakerRegularity`. These supply the common growth exponent
for derivative words and the character, smoothness and growth of those
derivatives. Applying `realUnequalPairConvergence` and
`realEqualPairConvergence` then gives the stated half-planes.

This is the convergence step of H. Jacquet, *Archimedean Rankin–Selberg
Integrals* (2009), formulas (2.4)–(2.6) and Theorem 2.1(i), author p. 6,
for the Library's exact compact-finite coefficient models. The thresholds
are the ones supplied by the general convergence estimates.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
