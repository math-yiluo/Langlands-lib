# Haar scaling of the adeles by a uniformizer at one finite place

Module `Langlands.Global.RankinSelberg.WhittakerCellAdelicScaling`, namespace
`Langlands.Global.RankinSelbergGlobal.WhittakerCellAdelicScaling`.

## Content

A helper module for the proof of the one-place Iwasawa cell decomposition
`WhittakerCellDecompositionStatement`. Its main results say that multiplication by the
idele `ι_v(ϖ)` scales additive Haar measure on `𝔸_F` by `N(v)⁻¹`, and multiplication by
`ι_v(ϖ) ^ k` scales it by `N(v) ^ (-k)`. Here `ϖ` is a uniformizer of `F_v` at a finite
place `v`, `ι_v(ϖ)` has component `ϖ` at `v` and `1` at every other place, and
`N(v) = Ideal.absNorm v.asIdeal`, the cardinality of the residue field at `v`. The Library
already has the archimedean analogue (`AdelicScalarHaarChar`), but has no finite-place
version.

### Counting cosets

- `measure_eq_card_mul`: let `J ≤ O` be additive subgroups of a measurable additive group,
  with `J` measurable, and let `ρ : O →+ k` be a surjective homomorphism onto a finite group
  whose kernel is `J`. Then every left-invariant measure `μ` satisfies
  `μ O = |k| · μ J`, because `O` is the disjoint union of the `|k|` translates of `J`.

### Valuations

- `le_one_of_mul_lt_one`: let `ϖ` be uniformizing for a valuation `w`
  (`IsUniformizingElement w ϖ`: `w ϖ < 1`, and every nonzero value is an integer power of
  `w ϖ`). Then `w (ϖ x) < 1` implies `w x ≤ 1`.
- `valuation F v`: the completion valuation `Valued.v` of `F_v`, with values in `ℤₘ₀`.
  This is the valuation used in `WhittakerCellDecompositionStatement`.

### The finite adeles

- `integralSubgroup F`: the integral finite adeles `Ô = ∏_w 𝒪_w` (the Library's
  `integralFiniteAdeles`), as an additive subgroup.
- `maximalSubgroup F v`: the subgroup `{y ∈ Ô : y_v ∈ 𝔪_v}`. `mem_maximalSubgroup`
  unfolds membership. `maximalSubgroup_le`: it lies in `Ô`. `isOpen_maximalSubgroup`: it
  is open.
- `norm_le_one_of_mem`: for `y ∈ Ô`, `‖y_v‖ ≤ 1`.
- `residue F v : Ô →+ 𝒪_v / 𝔪_v`: reduction of the `v`-component. `residue_apply` unfolds
  it. `residue_eq_zero_iff`: its kernel is `maximalSubgroup F v`. `residue_surjective`: it
  is surjective.
- `finiteSingle F v a`: the finite idele with component `a ∈ F_vˣ` at `v` and `1`
  elsewhere. `finiteSingle_apply_self` and `finiteSingle_apply_of_ne` give its
  components.
- `finiteSingle_mul_mem_iff`: for a uniformizer `ϖ`, `ι_v(ϖ) y ∈ maximalSubgroup F v`
  if and only if `y ∈ Ô`.
- `addEquivAddHaarChar_mulLeft_finiteSingle`: **finite-adelic scaling.** For a
  uniformizer `ϖ`, the additive Haar character of `y ↦ ι_v(ϖ) y` on the finite adeles is
  `N(v)⁻¹`.

### Units of a locally compact ring

`R` is a locally compact topological ring.

- `mulLeft_one`, `mulLeft_mul`: `r ↦ (x ↦ r x)` respects units and products.
- `mulLeftHaarChar : Rˣ →* ℝ≥0`: `r` goes to the additive Haar character of `x ↦ r x`.
  `mulLeftHaarChar_apply` unfolds it.

### The adeles

- `addEquivAddHaarChar_mulLeft_finiteIdeleInclusion`: **adelic scaling.** For a
  uniformizer `ϖ` of `F_v`, the additive Haar character of `x ↦ ι_v(ϖ) x` on `𝔸_F` is
  `N(v)⁻¹`. Here `ι_v(ϖ)` is the Library's `finiteIdeleInclusion F v ϖ`.
- `addEquivAddHaarChar_mulLeft_finiteIdeleInclusion_zpow`: for `k ∈ ℤ`, the additive
  Haar character of `x ↦ ι_v(ϖ) ^ k x` is `N(v) ^ (-k)`.

The measurable-space structures on `FiniteAdeles F` and `Adeles F` are hypotheses:
`[MeasurableSpace _] [BorelSpace _]`. The Haar character does not depend on the Haar
measure chosen.

## Proofs

`measure_eq_card_mul`: choose a preimage `r c ∈ O` of every `c ∈ k`. The translates
`T c = r c + J` are measurable, pairwise disjoint (`ρ` equals `c` on `T c`), and cover `O`
(`y ∈ T (ρ y)`). Each has measure `μ J` by left invariance, so
`μ O = ∑_c μ J = |k| · μ J`.

`le_one_of_mul_lt_one`: write `w x = (w ϖ) ^ n`. Then `(w ϖ) ^ (1 + n) < 1` forces
`1 + n > 0`, so `n ≥ 0` and `(w ϖ) ^ n ≤ 1`.

`residue_eq_zero_iff`: the residue of `y_v ∈ 𝒪_v` is zero exactly when `y_v ∈ 𝔪_v`, that
is when `‖y_v‖ < 1`, that is when `valuation F v (y_v) < 1`. `residue_surjective`: lift a
residue class to `x ∈ 𝒪_v` and take the finite adele with `x` at `v` and `0` elsewhere,
which lies in `Ô`. `isOpen_maximalSubgroup`: the subgroup is `Ô ∩ {y : ‖y_v‖ < 1}`, the
intersection of the open set `Ô` (Library `isOpen_integralFiniteAdeles`) with the preimage
of an open ball under the continuous evaluation at `v`.

`finiteSingle_mul_mem_iff`: at `w ≠ v`, `(ι_v(ϖ) y)_w = y_w`. At `v`, if `w(ϖ y_v) < 1`
then `w(y_v) ≤ 1` by `le_one_of_mul_lt_one`. Conversely, if `w(y_v) ≤ 1` then
`w(ϖ y_v) ≤ w(ϖ) < 1`.

`addEquivAddHaarChar_mulLeft_finiteSingle`: let `φ(y) = ι_v(ϖ) y` and `J` the maximal
subgroup, so that `φ⁻¹(J) = Ô` by the previous lemma. Coset counting for `residue F v`
gives `μ(Ô) = N(v) · μ(J)`, by the Library's `CompletionResidue.card_residueField`. Here
`0 < μ(J) < ∞`, since `J` is open and contained in the compact set `Ô`. Mathlib's
`addEquivAddHaarChar_smul_preimage` gives `δ(φ) · μ(φ⁻¹ J) = μ(J)`, that is
`δ(φ) · N(v) · μ(J) = μ(J)`. Cancelling `μ(J)` gives `δ(φ) N(v) = 1`.

`mulLeftHaarChar`: Mathlib's `addEquivAddHaarChar_refl` and `addEquivAddHaarChar_trans`.

`addEquivAddHaarChar_mulLeft_finiteIdeleInclusion`: as in the Library's
`AdelicScalarHaarChar`, the adeles are the product `𝔸_F = 𝔸_∞ × 𝔸_f` through the identity
map `e`. The product measure `μ = (μ_∞ × μ_f).map e` is an additive Haar measure. It is
regular, being left invariant and finite on compacts in a second-countable space
(`regular_of_isAddLeftInvariant`). Here `μ_∞` is the Lebesgue measure on the mixed space
moved to `𝔸_∞`, and `μ_f` is `addHaar` on `𝔸_f`. Multiplication by `ι_v(ϖ)` is
`id × (y ↦ ι_v(ϖ) y)`. The product of the image measures then gives
`N(v)⁻¹ · (x ↦ ι_v(ϖ) x)_* μ = μ_∞ × (N(v)⁻¹ · (y ↦ ι_v(ϖ) y)_* μ_f) = μ_∞ × μ_f`.
The Library's `addEquivAddHaarChar_eq_of_smul_map` turns this into the character.

`_zpow`: `mulLeftHaarChar` is a monoid homomorphism, so it sends `ι_v(ϖ) ^ k` to
`(N(v)⁻¹) ^ k = N(v) ^ (-k)`.

## Provenance

This is the standard fact that the module of `ϖ` on `F_v` is `|ϖ|_v = q_v⁻¹`, carried to
`𝔸_F` because `ι_v(ϖ)` is trivial at every other place. Cogdell (Fields lectures 2003,
Lecture 7 §3, p.57) uses it implicitly in the local formula `dh = dn δ_B⁻¹(ϖ^J) dk`. The
Lean proof is internal to this project: coset counting on the finite adeles together with
the product decomposition of `𝔸_F` used in `AdelicScalarHaarChar`.
