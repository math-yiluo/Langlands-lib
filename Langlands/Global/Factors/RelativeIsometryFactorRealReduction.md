# Relative isometry factors from real archimedean tests

`Langlands.Global.PoleComparison.relativeIsometryFactorStatement_of_realContinuation_and_tests`
proves `RelativeIsometryFactorRealReductionStatement.{uF,uW,uP,uE}`. Real uniform unequal-rank
continuation, real unequal-rank ordinary place tests with smaller group of rank at least two,
and real equal-rank ordinary place tests in ranks at least two imply the exact
`Langlands.Global.PoleComparison.RelativeIsometryFactorStatement.{uF,uW,uP,uE}`.
The conclusion ranges over all number fields, including those with real places, and all four
universe levels are independent.

## Archimedean inputs

`realPlaceUniformContinuationReduction` obtains the real-place functional equation from the
unequal continuation premise, `realLocalUniformPositiveEqualContinuation` and the contragredient
pair denominator comparison. The latter follows by applying `realPlaceContragredientPairLReduction`
to `Automorphic.cuspidalArchimedeanStandardIrreducible` and
`realStandardPairingPairLReduction realStandardDualPairing realStandardIntertwinerPairL`.

`complexPlaceWhittakerRange` realizes a complex model vector as an actual place restriction
with finite coordinate one. Apply it to the given adelic character and to its inverse, using
`complexComponent_complex_inv` to identify the inverse scale as \(-a\).
`complexOrdinaryPlaceTests_of_generation` then gives the complex tests from
`complexOrdinaryNormalizedGeneration`. On the real side,
`realUnequalOrdinaryPlaceTestsFromPositiveRank` supplies the smaller \(\mathrm{GL}_1\) case.
The equal-rank \(\mathrm{GL}_1\) case is included in
`archimedeanFactorizationOrdinaryReduction`. That theorem combines the four ordinary test
assertions with `infiniteWhittakerSliceModel` and the real-place equation to give the
archimedean factorizations. They combine with the two place equations and
`archimedeanCentralSign` to give `ArchimedeanSemilocalTheoryStatement`, using
`complexPlaceFunctionalEquation` for the complex places.

For the alternative using real normalized generation,
`relativeIsometryFactorStatement_of_realContinuation_and_generation` applies
`realOrdinaryPlaceTests_of_generation` with `realWhittakerRestrictionOnto`.
The restriction theorem applies to arbitrary cuspidal realizations.

## From the functional equation to the relative factors

`unequalSemilocalArchimedeanReduction` supplies the unequal-rank semilocal equation.
`equalSemilocalFactorization_of_archimedeanSemilocalTheory` and `equalSemilocalReduction`
supply its equal-rank counterpart. `cuspidalPairPartialGammaGlobalReduction` assembles them
with the analytic, unfolding, Euler factorization and dual Euler factorization theorems in
both rank cases:

- `UnequalAnalytic.unequalAnalyticStatement_proof`, `unequalUnfoldingStatement_proof`,
  `unequalEulerFactorization`, `unequalDualEulerFactorization`.
- `EqualAnalytic.equalAnalyticStatement_proof`, `equalUnfoldingStatement_proof`,
  `equalEulerFactorization`, `equalDualEulerFactorization`.

`cuspidalPairCompletedEquation_of_satakeBound_of_partialGamma` uses
`cuspidalSatakeBoundReduction Automorphic.OperatorRealization.irreducibleCentralCharacter`
to obtain the completed equation. `cuspidalPairFunctionalEquationReduction` combines it
with `cuspidalPairLocalData` and `cuspidalArchimedeanParameterExistence`.

`associatedGamma_of_inputs` uses that functional equation and `stableTwistPairGammaMatchStatement`
to compare the finite-place gamma factors. `associatedTemperedFactor_of_gamma_and_existence`
uses `LocalClassField.commonClosureReciprocityExistence` and
`LocalFactor.NonabelianSystem.exists_system` to obtain the tempered comparison.
`relativeIsometryFactorStatement_of_tempered` applies it to the tempered local inductions
given by the unitary supports of the witnessed generators. The local determinant identity,
the pair comparisons on the signed spans, and the additive character change give the
conclusion.

## Sources

- H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), author-posted pp. 6–10,
  equations (2.4)–(2.6), Theorem 2.1, and Theorems 2.3, 2.6 and 2.7. The real hypotheses
  concern the ordinary and reflected integrals in Theorem 2.1 and the nonvanishing
  needed for the ordinary tests. `jacquet-2009-archimedean-rankin-selberg`,
  SHA-256 `7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
- J. W. Cogdell, *Analytic theory of L-functions for GLₙ* (2004), proof of Theorem 4.1,
  printed pp. 219–220 (PDF pp. 222–223). The local tests, global integrals and local
  functional equations give the completed equation. `cogdell-2004-analytic-theory-gln`,
  SHA-256 `8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
  p-adique* (2000), §2.3 and its Corollary, printed pp. 444–445 (PDF pp. 6–7), and
  §2.6 Proposition (a)–(b), printed pp. 446–447 (PDF pp. 8–9). The theorem uses the
  corresponding relative comparison on witnessed generators. `henniart-2000-simple-proof`,
  SHA-256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
