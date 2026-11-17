# Real-place reduction to the analytic restriction equations

This internal adapter uses Worker 3657's real standard-module nonvanishing
theorem. Its four paired helper modules are included in the same contribution:
`InversePowerFourier`, `RealGramFunction`, `RealStandardBlockPolynomial` and
`RealStandardNontrivialProof`. They also supply the nonvanishing input for
Task 7003.

The main proposition is
`RealPlaceAnalyticReductionStatement.{u}`: the exact published
`RealPlaceFunctionalEquationStatement.{u}` follows from
`RealJacquetRestrictionEquationStatement.{u}`. The field universe is free.
This remains a conditional intermediate result: the full analytic package for
actual global Whittaker restrictions is the retained premise.

The theorem `realPlaceAnalyticReduction` proves this implication. The adapter
specializes `Langlands.Archimedean.realStandardNontrivial` at
`n = realRank ds`. Nontriviality supplies a vector different from zero by
`exists_ne 0`, proving the existing `RealStandardKFiniteNonzeroStatement`.
The previously proved `realPlaceAnalyticNonzeroReduction` then discharges the
remaining algebraic premise.

The nonvanishing theorem constructs a Gram function of a block polynomial,
checks its principal-series transformation law and compact-finiteness,
and shows that its value at identity is nonzero. Its induced-block Fourier
conditions follow from an explicit two-row rotation computation and a
Cauchy-integral vanishing lemma. The implementation is described in the four
helpers' paired Markdown.

Combining that theorem with the parameter-determinant and reflection reductions
discharges all of their retained algebraic premises. The one remaining premise,
`RealJacquetRestrictionEquationStatement`, still includes convergence,
holomorphy, meromorphic continuation, both source-convention equations for
actual global restrictions, local-model membership and normalization
identification. It is not proved here. In particular this contribution does
not prove the unconditional real-place functional equation or complete
Task 7400.

All five modules compile together in the pinned environment, with no errors or
warnings (check `72836723-7d39-41ef-9c5b-1d032346f939`). Inspection confirms that
the entry proposition returns `Prop` and retains its free universe parameter
`u`. The adapter has internal provenance and quotes no new analytic theorem.

Check `650bc6d6-f02e-45c5-8d3e-afeb98d47fda` inspects the implemented theorem `realPlaceAnalyticReduction`: its universe parameter `u` is free and its only axioms are `propext`, `Classical.choice` and `Quot.sound`.
