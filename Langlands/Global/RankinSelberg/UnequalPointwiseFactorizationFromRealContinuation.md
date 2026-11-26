# Unequal pointwise factorization from real continuation and ordinary tests

`UnequalPointwiseFactorizationFromRealContinuationStatement` gives
`UnequalPointwiseFactorizationStatement.{u,uQ}` from three premises:
`RealLocalUniformUnequalContinuationStatement`,
`RealUnequalOrdinaryPlaceTestsStatement.{u}`, and
`ComplexUnequalOrdinaryPlaceTestsPositiveRankStatement.{u}`. The complex premise
concerns smaller rank at least two. Each ordinary test uses one pair of actual
place restrictions and a compatible quotient measure for every right
half-plane. The field and spectral presentation universes remain independent.

## Real unequal-rank equation

`realUnequalFunctionalEquation_of_uniformContinuation` uses
`realPlaceUniformWhittakerModel` to put the two actual real restrictions in the
uniform Whittaker models for the parameters \(a\) and \(-a\). The theorem
`realLocalUniformUnequalJacquet_of_continuation` adds convergence and holomorphy
of both integrals to the continuation premise. The local block lists for the
dual are compared with the supplied contragredient place parameters by
`realPlaceContragredientPairLReduction`. Its comparison comes from irreducibility
of the actual standard modules and invariance of their pair denominators under
the local dual pairing.

Let \(c\) and \(d\) be the minus-one scalars of the larger and smaller
representations, with ranks \(r+1\) and \(t+1\). The comparisons
`realMinusOneScalar_eq_parameter` replace the inducing determinants by \(c\)
and \(d\) in the source-convention sign \(c^{t+1}d\).
`pair_epsilon_neg` and the pair central compatibility identity replace the
epsilon at \(-a\) by the epsilon at \(a\) multiplied by
\(c^{t+1}d^{r+1}\). Their product is the required sign \(d^r\), since
\(c^2=d^2=1\). `EquationPackage.change_factor` transfers the equation using
this pointwise identity.

## Global assembly

`realUnequalPlaceTests_of_ordinary` applies that equation to each ordinary
real-place test. A nonzero ordinary value in the convergence half-plane
ensures that the reflected dual continuation is nonzero, so the same pair and
measure supply the joint test. `infiniteWhittakerSliceModel` supplies the
simultaneous Whittaker slice comparison. The proof then applies
`unequalPointwiseFactorizationFromOrdinary`, which supplies the smaller
complex rank-one case, transfers complex ordinary tests to joint tests, and
assembles the pointwise identities and nonvanishing.

This is an internal reduction of the pointwise step in J. W. Cogdell,
*Analytic Theory of L-Functions for GLₙ*, proof of Theorem 4.1, printed p. 219
(`cogdell-2004-analytic-theory-gln`). The real local analytic input follows the
form of the unequal-rank integrals and continuation in H. Jacquet,
*Archimedean Rankin–Selberg integrals*, (2.4)–(2.5) and Theorem 2.1, author p. 6
(`jacquet-2009-archimedean-rankin-selberg`). The resulting local sign agrees
with the unequal-rank convention in Cogdell's Theorem 3.6, printed p. 217.
