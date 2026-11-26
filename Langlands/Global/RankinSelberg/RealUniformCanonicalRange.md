# The canonical real Jacquet range and its continuous smooth evaluation

For parities `p : Fin (r + 1) → Fin 2` and exponents `z : Fin (r + 1) → ℂ`, let
`characterList p z` be the corresponding list of real characters and
`canonicalJacquetMap a p z` the Library's canonical (meromorphically continued) Jacquet map
with parameter `a ∈ ℝˣ` on its `O(r+1)`-finite standard module
(`RealGodementCanonicalCoefficient`). The Library's real equal-rank growth step
`RealGodement.realLocalEqualGrowthStep` (module `RealLocalEqualGrowthStep`) takes two
hypotheses about these maps:

* `RealUniformCanonicalRangePremise`: for all `r, a, p, z`, the uniform Whittaker model
  `realUniformWhittakerModel r (characterList p z) (-a)` lies in the range of
  `canonicalJacquetMap a p z`;
* `RealCanonicalStandardEvaluationPremise`: for all `r, a, p, z`, there is a continuous
  linear functional `L` on the genuine smooth vectors of the compact Banach completion with
  `IsWhittakerStandardEvaluation (characterList p z) (-a) (canonicalJacquetMap a p z) L`.

## Statement

`RealCanonicalRangeAndEvaluationStatement` is the conjunction
`RealUniformCanonicalRangePremise ∧ RealCanonicalStandardEvaluationPremise`.
`realCanonicalRangeAndEvaluation` proves it, from the two theorems below. Mathematically the
first premise is uniqueness up to scalars of the Whittaker coefficient maps of a real character
principal series, the canonical map being the continued Jacquet integral; no continuity of the
coefficient maps is assumed. It is an internal step of the real local theory of
Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), where the Whittaker models of the
principal series are given by Jacquet integrals.

## Proof

* `exists_canonicalStandardEvaluation` and `realCanonicalStandardEvaluationPremise`: the
  canonical map is a specified Whittaker intertwiner for `-a` (`realGodementCanonicalModel`),
  and `characterList p z` is the image of a list of real character data, so
  `exists_standardEvaluation` (module `RealExactStandardEvaluation`) gives the continuous
  evaluation.
* `hasBoundedCanonicalEvaluation`: the Library's `exists_boundedForm_of_characterEvaluation`
  (module `RealAscendingWhittakerEvaluation`) turns that continuous Whittaker functional into a
  compact-derivative-bounded Whittaker form on the full smooth position principal series whose
  coefficient map is the canonical map; this is `HasBoundedCanonicalEvaluation a p z` at every
  parameter, not only in the convergent chamber.
* `uniformWhittakerModel_le_range` and `realUniformCanonicalRangePremise`: the uniform model is
  the supremum of the ranges of uniform Whittaker coefficient maps `B`. For each such `B`,
  `exists_standardEvaluation` and `exists_boundedForm_of_characterEvaluation` give a bounded
  Whittaker form whose coefficient map is `B`. The Library's comparison
  `functionalCoefficient_eq_smul_canonical` (module `RealCanonicalWhittakerComparison`, based
  on the distributional Whittaker uniqueness of the principal series), applied with
  `hasBoundedCanonicalEvaluation`, gives a scalar `c` with `B = c · canonicalJacquetMap a p z`;
  hence `B f = canonicalJacquetMap a p z (c f)` lies in the range.

This is the real counterpart of the complex multiplicity-one argument of the Library's
`ComplexJacquetMultiplicityOne`.
