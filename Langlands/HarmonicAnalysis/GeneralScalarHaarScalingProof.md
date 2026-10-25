# Residue-normalized scalar Haar scaling over general local fields

Author: Worker 11.

This module proves the existing proposition
`Langlands.HarmonicAnalysis.GeneralScalarHaarScalingStatement.{uF} F` of
[GeneralHaarScalingStatement](GeneralHaarScalingStatement.md) without changing
its statement or imported definitions. The field universe remains arbitrary.
The closing theorem `Langlands.HarmonicAnalysis.generalScalarHaarScalingStatement`
has exactly the published proposition as its complete type, for every
nonarchimedean local field `F` (a field with a `ValuativeRel` and a topology
satisfying `IsNonarchimedeanLocalField F`), including fields of positive
characteristic.

Concretely, let `q` be the cardinality of the residue field of the valuation
ring of `ValuativeRel.valuation F`, let `abv : AbsoluteValue F ℝ` and the field
unit `ϖ` satisfy the three premises of the statement (`ϖ` is a uniformizing
element, `abv ϖ = q⁻¹`, and `abv x = 1` whenever the valuation of `x` is one).
Then for any Borel measurable structure on `F`, any additive Haar measure `μ`
and any field unit `a`,

`μ.map (fun x => (a : F) * x) = ((Shahidi.absUnits abv a : ℝ≥0)⁻¹) • μ`.

The proof adds no regularity, countability, completeness or normalization
premise: these properties are derived from `IsNonarchimedeanLocalField F`.

## Intrinsic topology API

The following theorems are public in `Langlands.HarmonicAnalysis.GeneralLocalField`,
with the field `F` as explicit argument. They are theorems for explicit
installation, not new global instances.

- `properNormedField` produces a `NontriviallyNormedField F` whose topology is
  the given topology of `F` and which is a proper metric space. It follows the
  construction in Mathlib's `CompleteSpace` instance for
  `IsNonarchimedeanLocalField`: install the right uniform structure of the
  additive group, equip `ValuativeRel.valuation F` with a rank-one structure
  from `ValuativeRel.IsRankLeOne`, and take `Valued.toNontriviallyNormedField`.
  The topology equality holds by `rfl`, and properness is
  `ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`.
- `secondCountableTopology` applies `secondCountable_of_proper` to that normed
  structure and rewrites the topology.
- `sigmaCompactSpace` follows from second countability and local compactness
  by Mathlib's instance.
- `pseudoMetrizableSpace` uses that the uniformity of a pseudometric space is
  countably generated; `t2Space` uses that the normed field is a metric space.
  Both rewrite along the topology equality of `properNormedField`.
- `haarMeasure_regular` states that every additive Haar measure for any Borel
  measurable structure on `F` is regular. Sigma compactness and
  pseudometrizability give regularity through Mathlib's
  `Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`.
- `isCompact_integer` and `isOpen_integer` state that the valuation ring
  `𝒪[F]` is compact (Mathlib's `IsNonarchimedeanLocalField.isCompact_closedBall`
  at radius one) and open (`Valuation.isOpen_integer`).

## Implemented proof

Write `v = ValuativeRel.valuation F` and `O = 𝒪[F]`. The remaining helper
theorems are private.

1. *Index formula.* Pull `μ` back to `O` along the measurable embedding of the
   open set `O`; the pullback is additively left invariant. The additive
   subgroup underlying the maximal ideal of `O` is open (Mathlib's
   `IsLocalRing.isOpen_maximalIdeal`, using compactness of `O`, Hausdorffness
   and that `O` is a discrete valuation ring), and its index is the
   cardinality of the residue field, which is finite. Then
   `AddSubgroup.index_mul_measure` gives
   `Nat.card 𝓀[F] * μ(maximal ideal, as a subset of F) = μ(O)`.
2. *Balls.* For a field unit `a`, `a • O = {x | v x ≤ v a}`, by multiplicativity
   of `v`.
3. *Uniformizer.* For a uniformizing element `ϖ`, `v x < 1 ↔ v x ≤ v ϖ`. For
   nonzero `x` write `v x = (v ϖ)^m`; since `0 < v ϖ < 1`, integer powers of
   `v ϖ` are strictly antitone (`zpow_right_strictAnti₀`), so `v x < 1` forces
   `m ≥ 1`. Hence `ϖ • O` is the maximal ideal, using the valuation criterion
   for nonunits of the valuation ring.
4. *Haar character.* `O` has positive finite Haar measure (open and compact).
   With the derived regularity, Mathlib's `distribHaarChar_mul` and steps 1
   and 3 give `q * distribHaarChar F ϖ * μ(O) = μ(O)`; cancelling `μ(O)` gives
   `distribHaarChar F ϖ = q⁻¹` (here `q > 1` because the residue field is a
   finite field). For a general field unit `a`, write `v a = (v ϖ)^m`. The
   balls `a • O` and `ϖ^m • O` coincide by step 2, so after cancelling `μ(O)`
   their Haar characters agree, and `distribHaarChar F a = q^(-m)`.
5. *Absolute value.* The unit `a * (ϖ⁻¹)^m` has valuation one, so the premise
   on `abv` gives `Shahidi.absUnits abv (a * (ϖ⁻¹)^m) = 1`, and multiplicativity
   gives `Shahidi.absUnits abv a = (Shahidi.absUnits abv ϖ)^m = q^(-m)`. Thus
   `distribHaarChar F a = (Shahidi.absUnits abv a : ℝ≥0)`.
6. *Pushforward.* Evaluate on a measurable set `s`: the preimage of `s` under
   multiplication by `a` is `a⁻¹ • s`, and `distribHaarChar_mul` with step 5
   at `a⁻¹` gives the factor `(Shahidi.absUnits abv a)⁻¹`. Measure
   extensionality completes the proof.

## Provenance and scope

This is an internal derived proof of the already published general-field scalar
prerequisite. It mirrors the route of the p-adic proof
[PadicScalarHaarScalingProof](PadicScalarHaarScalingProof.md), replacing the
p-adic normalization data by the valuation, uniformizing element and absolute
value quantified in the general statement, and replacing finite dimensionality
over `ℚ_p` by Mathlib's normed structure on a nonarchimedean local field. It
uses Mathlib's Haar uniqueness, finite-index measure formula and local-field
topology results. It introduces no literature statement and no new
normalization. The rectangular and block-modulus statements of the same module
are not proved here.
