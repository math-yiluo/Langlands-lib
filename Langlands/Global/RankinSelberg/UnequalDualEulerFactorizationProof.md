# Proof of the unequal-rank dual Euler factorization

Module `Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationProof`, namespace
`Langlands.Global.RankinSelbergGlobal`.

## Main result

The theorem `unequalDualEulerFactorization` proves the published proposition
`Langlands.Global.RankinSelbergGlobal.UnequalDualEulerFactorizationStatement` (module
`Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationStatement`). The proposition is
unchanged, and both of its universe parameters `u` (number fields) and `uQ` (spectral
presentations) remain free. The proposition is the partial Euler factorization of the
unequal-rank dual global Whittaker integral of Cogdell 2004 (source
`cogdell-2004-analytic-theory-gln`, §§2.2, 4.1).

## Proof

The proof applies two published conditional results to published proofs. It adds no new
mathematics.

1. `unequalUnfolding_of_gaugeProofs : UnequalUnfoldingStatement.{u}` is the term
   `unequalUnfolding_of_whittakerGauges unequalPadGauge (unequalRectGauge_of_simpleRootGauge
   whittakerSimpleRootMajorization adelicSimpleRootGaugeRectangularMellin)`, built from these
   published results:
   - `unequalUnfolding_of_whittakerGauges` (module `UnequalUnfoldingAssembly`) derives
     `UnequalUnfoldingStatement` from the two Whittaker gauge statements
     `UnequalPadGaugeStatement` and `UnequalRectGaugeStatement`;
   - `unequalPadGauge` (module `UnequalPadGaugeProof`) proves `UnequalPadGaugeStatement`;
   - `unequalRectGauge_of_simpleRootGauge` (module `UnequalRectGaugeOfSimpleRootGauge`)
     derives `UnequalRectGaugeStatement` from `WhittakerSimpleRootMajorizationStatement` and
     `AdelicSimpleRootGaugeRectangularMellinStatement`;
   - `whittakerSimpleRootMajorization` (module `WhittakerSimpleRootMajorization`) and
     `adelicSimpleRootGaugeRectangularMellin` (module `RectangularGaugeMellinProof`) prove
     these two statements.
2. `unequalDualEulerFactorization` is
   `UnequalDualEulerContragredient.unequalDualEulerFactorizationUnfoldingReduction` (module
   `UnequalDualEulerFactorizationUnfoldingReduction`) applied to
   `unequalUnfolding_of_gaugeProofs`. That reduction proves
   `UnequalUnfoldingStatement → UnequalDualEulerFactorizationStatement`. Its Markdown describes
   the argument: absolute convergence of the dual integral from the unfolding, the splitting
   of the dual Whittaker functions at unramified places, and the cell decomposition at each
   unramified place.

All module names above are in `Langlands.Global.RankinSelberg`. The proof uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.
