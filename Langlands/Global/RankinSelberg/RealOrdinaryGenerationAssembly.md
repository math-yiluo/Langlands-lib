# Assembly of real ordinary normalized generation

`RealOrdinaryGenerationAssemblyStatement` takes three hypotheses. These are
exact ordinary real normalized continuation, polynomiality for the real
character lists in the adjacent and equal rank families at the standard
scales, and `RealGaussianRowsDenseStatement`. The density statement concerns
complex polynomial times Gaussian functions at scale \(\pi\) in the Schwartz
topology on every positive-dimensional real row space. Under these hypotheses
`realOrdinaryGenerationAssembly` gives the full proposition
`RealOrdinaryNormalizedGenerationStatement`.

Pointwise coverage for both families follows from
`realOrdinaryPointwiseCoverage`. The polynomial reduction transfers the
character-list hypothesis to the original block lists. At equal ranks, fix
the two compact-finite coefficients that detect a given spectral point.
Continuous normalized evaluation in the Schwartz row transfers that
nonvanishing to a polynomial Gaussian row, by density. At adjacent ranks the
whole ordinary test family has polynomial values under the polynomiality
hypothesis. The two polynomial-ideal generation results give finite sums equal
to one at the standard scales. All the tests keep their supplied quotient
measure and exact coefficient models.

The assembly uses the polynomial recursion, pointwise generation and
polynomial ideal argument in [Jacquet, *Archimedean Rankin–Selberg integrals*, §8.4 and §§14–15](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
