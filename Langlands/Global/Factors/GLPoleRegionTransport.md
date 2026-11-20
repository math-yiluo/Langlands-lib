# Transport lemmas for the GL pole-region statement

This internal module supports the proof `Langlands.Global.glPairPoleRegion` of
`Langlands.Global.GLPairPoleRegionStatement` (Henniart 1986, Proposition 4.5(ii),
`GL_n` side). The statement quantifies every realization `T` of a p-adic field. It
uses the JPSS relations `IsEqualRankLPolynomial` and `IsUnequalRankLPolynomial`,
together with normalized generators of the dual-pair zeta values. The Library's
local-factor theorems are stated for the canonical realization and the relation
`IsPadicPairLPolynomial` (or its symmetric form `IsPadicSymmetricLPolynomial`).
This module connects the two. All results are derived here from published
definitions and theorems; none is a literature statement.

## Every realization is the canonical one

Namespace `Langlands.PadicField.TopologicalData`.

- `vle_one_iff_canonicalNorm_le_one T x`: `x ≤ᵥ 1` for the valuative relation of
  `T` exactly when `F.canonicalNorm x ≤ 1`. It rewrites with the published
  `T.canonicalNorm_le_one_iff_mem_integers` and uses that the valuation of `T`'s
  valuative relation is at most one exactly on its integers.
- `valuativeRel_eq_canonical T`: `T.valuativeRel` is the valuative relation of
  `F.canonicalTopologicalData`. For `y = 0` both sides are `x = 0`
  (`ValuativeRel.vle_zero_iff`). For `y ≠ 0`, `x ≤ᵥ y ↔ x / y ≤ᵥ 1`
  (`ValuativeRel.div_vle_one_iff`), and the previous lemma applies to both relations.
- `ext_of_topology_valuativeRel`: two realizations with the same topology and the
  same valuative relation are equal, because their other fields are proofs.
- `eq_canonicalTopologicalData T : T = F.canonicalTopologicalData`. The topologies
  agree by the published `topology_eq_canonicalModule` applied to `T` and to the
  canonical realization, and the valuative relations by the previous lemma.

## The unequal-rank relation does not depend on the Haar measure

Namespace `Langlands.RankinSelberg`.

- `zetaSpan_unequalRankValuesOf_smul_rectangular`: replacing the measure `ν` on
  the rectangular matrix variable by `c • ν`, with `c ≠ 0, ∞`, leaves the Laurent
  span of the unequal-rank zeta values unchanged. Convergence is unchanged
  (`Measure.prod_smul_right`, `integrable_smul_measure`). Each integral is
  multiplied by the real constant `c.toReal`. The published
  `zetaSpan_eq_of_const_mul` and `hasRationalContinuation_const_mul` then identify
  the spans.
- `isUnequalRankLPolynomial_smul_rectangular`: hence
  `IsUnequalRankLPolynomial … (c • ν) π π' P ↔ IsUnequalRankLPolynomial … ν π π' P`,
  by `isNormalizedGenerator_congr`.
- `AdditiveHaarMeasure.exists_eq_smul`: two additive Haar measures differ by a
  positive scalar `κ`. This is Mathlib's `isAddLeftInvariant_eq_smul_of_regular`
  with `addHaarScalarFactor`.
- `isUnequalRankLPolynomial_rectangular_congr`: the relation at
  `rectangularMeasure ν j (n + 1)` is equivalent to the relation at
  `rectangularMeasure ν₀ j (n + 1)`. The published `rectangularMeasure_eq_smul`
  writes the first measure as `κ^(j(n+1)) •` the second.

## From the statement's relations to p-adic pair L-polynomials

Namespace `Langlands.Global.GLPoleRegion`. Everything is over
`F.canonicalTopologicalData`.

- `eq_of_isEqualRankLPolynomial`: if `IsPadicPairLPolynomial F ψ ν π σ P₀`, then
  every `P` with `IsEqualRankLPolynomial q ψ abv μ π σ P` at a compatible `μ`
  equals `P₀`. The second clause of `IsPadicPairLPolynomial` at `μ`, unfolded by
  `isPairLPolynomial_self`, is the same relation, and normalized generators are
  unique (`IsNormalizedGenerator.unique`).
- `eq_of_isUnequalRankLPolynomial`: the same in unequal rank. The relation may be
  given at `rectangularMeasure ν j (n + 1)` for any additive Haar `ν`, while the
  pair relation uses `ν₀`. The Haar-change lemma above handles this.
- `isPadicPairLPolynomial_of_equalRank ν νd hπ hσ`: let `π` be generic for `ψ`
  and `σ` generic for `ψ⁻¹ = ψ.scale (-1)` on `GL_(n+1)`. Let `P` satisfy the
  equal-rank relation of the statement, and `Pdual` be the normalized generator of
  the dual values at a compatible `μ`. Then `P` is the p-adic pair L-polynomial of
  `(π, σ)` for `ψ` at `ν`. Also `Pdual` is that of `(π^ι, σ^ι)` for `ψ.scale (-1)`
  at `νd`, where `π^ι` is `inverseTransposePullback π`. The two Haar measures
  `ν`, `νd` are arbitrary.
  - Generic representations have Whittaker type (`isOfWhittakerType_of_isGeneric`).
  - For `σ`, the standard character of `ψ.scale (-1)` is rewritten as
    `inverseStandardCharacter ψ n` (`standardCharacter_scale_neg_one`).
  - The published `padicPairLPolynomial_isPadic` gives p-adic pair L-polynomials
    `P₀` of `(π, σ)` and of the dual pair. For the dual pair it uses
    `isOfWhittakerType_firstDual` and `isOfWhittakerType_secondDual`.
  - The dual values of the statement are by definition the values of
    `(π^ι, σ^ι)` for `ψ.scale (-1)`. So the previous lemma identifies `P` and
    `Pdual` with these polynomials.
- `isPadicPairLPolynomial_of_unequalRank ν₀ νd hπ hσ`: the same in unequal rank,
  for `π` on `GL_(n+(j+k+1)+1)` and `σ` on `GL_(n+1)`, block `j`. It holds for
  every additive Haar `ν` in the statement's rectangular measure.

## Zero-free disks

`hasNoReflectedCommonZero_of_radii`: suppose `P` has no zero in `‖z‖ < R`,
`Pdual` has no zero in `‖w‖ < R'`, `R' ≥ 0` and `q R R' > 1`. Then
`HasNoReflectedCommonZero q P Pdual`. A reflected common zero `z ≠ 0` would give
`‖z‖ ≥ R` and `‖q⁻¹ z⁻¹‖ ≥ R'`, hence `q R R' ≤ q ‖z‖ R' ≤ 1`.

## Dependencies

The module imports the published modules `Global/Factors/GLPoleRegionStatement`,
`LocalField/Normalization/Proof`, `RankinSelberg/PadicPairFactors`,
`RankinSelberg/UnequalRankDualCharacterChange`,
`RankinSelberg/HighlyRamified/EssentialInput`, `RankinSelberg/PairLFactor` and
`RankinSelberg/PadicGenericDualLFactor`. It introduces no axioms and no
hypotheses.
