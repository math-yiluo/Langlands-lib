# Theorem 2.7 over every local field: from supplied data to hypothesized normalization

Module `Langlands.Representation.RankinSelberg.LocalFieldUnequalRankAnalyticReduction`
(part of the proof of `SphericalCorankOneFunctionalEquationStatement`).

## Context

Jacquet, Piatetski-Shapiro and Shalika 1983, Theorem (2.7)(i)–(ii) (printed page 390)
asserts that the unequal-rank block integrals converge absolutely on a right half-plane,
have rational continuations, admit a common denominator and have a normalized generator.
The all-field port states this as
`Langlands.AllField.RankinSelberg.UnequalRankAnalyticStatement F T n j k`. It takes a field
`F` with supplied data `T : LocalFieldData F`, which fixes the topology, the valuation, the
Borel structures, the residue cardinality `T.residueCardinality` and the absolute value
`normalizedAbsoluteValue T`.

`LocalFieldUnequalRankAnalyticStatement` states the same conclusion
(`UnequalRankAnalyticConclusion`) with ambient instances and arbitrary Borel structures. It
takes a hypothesized residue cardinality `q` and an absolute value `abv` with
`abv ϖ = q⁻¹` for a uniformizing element `ϖ` and `abv x = 1` on valuation units.

## Theorem `localFieldUnequalRankAnalytic_of_allField`

Hypothesis: for every nonarchimedean local field `F` (in universe `uF`) and every `n, j, k`,
`UnequalRankAnalyticStatement F (LocalFieldData.ofInstances F) n j k` holds.
Conclusion: `LocalFieldUnequalRankAnalyticStatement`.

Proof as implemented:
1. Every Borel structure in the target context (on `F`, `GL_(n+1)(F)`, the upper
   unipotent group and the quotient `N\GL`) equals the `borel` structure. The proof
   substitutes these equalities (`BorelSpace.measurable_eq`).
2. `eq_normalizedAbsoluteValue_ofInstances` (all-field module
   `LocalFieldUnequalRankFunctionalEquationReduction`) shows that `abv` is
   `normalizedAbsoluteValue (LocalFieldData.ofInstances F)`. `residueCardinality_ofInstances`
   shows that `q` is `(LocalFieldData.ofInstances F).residueCardinality`. The proof
   substitutes both.
3. The topology and valuation of `LocalFieldData.ofInstances F` are the ambient ones by
   definition. The hypothesis at `F, n, j, k` then applies to the remaining arguments
   unchanged.

This follows `localFieldUnequalRankFunctionalEquation_of_allField` (the same all-field
module), which does the same for the functional equation.

## Theorem `localFieldUnequalRankAnalytic`

Conclusion: `LocalFieldUnequalRankAnalyticStatement`, with no hypotheses.

Proof as implemented: apply `localFieldUnequalRankAnalytic_of_allField` to the published
all-field theorem `Langlands.AllField.RankinSelberg.unequalRankAnalytic F
(LocalFieldData.ofInstances F) n j k` (module
`Langlands.AllField.Representation.RankinSelberg.UnequalRankAnalyticProof`).
