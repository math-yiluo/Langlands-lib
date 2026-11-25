# Real-place reduction to the analytic restriction equations

This internal adapter uses the real standard-module nonvanishing
theorem. Its four paired helper modules were ported together with this module:
`InversePowerFourier`, `RealGramFunction`, `RealStandardBlockPolynomial` and
`RealStandardNontrivialProof`. They also supply the nonvanishing input for
the genericity statement `CuspidalArchimedeanStandardGenericStatement`.

The main proposition is
`RealPlaceAnalyticReductionStatement.{u}`: the exact Library statement
`RealPlaceFunctionalEquationStatement.{u}` follows from
`RealJacquetRestrictionEquationStatement.{u}`. The field universe is free.
This remains a conditional intermediate result: the full analytic package for
actual global Whittaker restrictions is the retained premise.

The theorem `realPlaceAnalyticReduction` proves this implication. The adapter
specializes `Langlands.Archimedean.realStandardNontrivial` at
`n = realRank ds`. Nontriviality supplies a vector different from zero by
`exists_ne 0`, proving the existing `RealStandardKFiniteNonzeroStatement`.
The Library theorem `realPlaceAnalyticNonzeroReduction` then discharges the
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
identification. It is not proved here. In particular this module does
not prove the unconditional real-place functional equation.

All five modules compile together in the pinned environment, with no errors or
warnings. Inspection confirms that
the entry proposition returns `Prop` and retains its free universe parameter
`u`. The adapter has internal provenance and quotes no new analytic theorem.

An inspection of the implemented theorem `realPlaceAnalyticReduction` shows that its universe parameter `u` is free and its only axioms are `propext`, `Classical.choice` and `Quot.sound`.
