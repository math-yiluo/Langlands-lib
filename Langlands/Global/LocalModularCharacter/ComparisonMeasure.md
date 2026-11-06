# Bounding the modular character by a locally comparable measure

Module `Langlands.Global.LocalModularCharacter.ComparisonMeasure`.

This module contains the measure-theoretic core of the proof that the modular character of the
local points `G(K)` of a smooth affine group scheme is `|det Ad|`. It does not mention group
schemes or local fields. Everything happens on a group `H` that is a locally compact, Hausdorff,
second-countable topological group with its Borel σ-algebra.

Conventions are Mathlib's: `Measure.modularCharacter g` is the factor with
`map (· * g) μ = modularCharacter g • μ` for any left Haar measure `μ`.

## Main result

`modularCharacter_le_of_comparison ν g D hpos happrox hdet : modularCharacter g ≤ D`.

Hypotheses, for a finite measure `ν` on `H` (in applications, Lebesgue measure on a chart
neighbourhood of `1`, pulled back to `H`), an element `g` and a real `D ≥ 0`:

- `hpos`: `0 < ν U` for every neighbourhood `U` of `1`.
- `happrox`: for every `η > 0` there is a neighbourhood `N` of `1` such that
  `ν (x • T) ≤ (1 + η) ν T` for every `x ∈ N` and every measurable `T ⊆ N`.
- `hdet`: for every `η > 0` and every neighbourhood `U` of `1` there is an open `V ⊆ U`
  containing `1` with `ν (g V g⁻¹) ≤ (1 + η) D ν V`.

The module proves only an upper bound. The task needs equality, and that comes later from
multiplicativity: apply the bound to `g` and to `g⁻¹`.

## Auxiliary lemmas

- `measure_conj_image`: `μ (g V g⁻¹) = modularCharacter g * μ V` for a left Haar measure `μ` and
  any set `V`. Proof: left invariance, together with Mathlib's identification of the modular
  character with `haarScalarFactor (map (· * g) μ) μ`.
- `mconv_restrict_apply`: for measurable `S`,
  `(μ ∗ₘ ν.restrict W) S = ∫⁻ x, ν (W ∩ x⁻¹ S) ∂μ`. This unfolds Mathlib's `Measure.mconv`
  (the image of the product measure under multiplication) using `Measure.prod_apply`.
- `isMulLeftInvariant_mconv_restrict`: the convolution `μ ∗ₘ ν.restrict W` is left-invariant,
  because the integral formula is invariant under left translation of `μ`.
- `isFiniteMeasureOnCompacts_mconv_restrict`: if `ν` is finite and `W ⊆ K` with `K` compact,
  the convolution is finite on compacts. For compact `C`, the integrand vanishes outside
  `C K⁻¹` and is bounded by `ν univ`.
- `lintegral_measure_translate_inter`: `∫⁻ x, ν (x W ∩ S) ∂μ = μ W⁻¹ * ν S` for measurable `W`
  and `S`. This applies Fubini (`prod_apply` and `prod_apply_symm`) to the measurable set
  `{(x, y) | x⁻¹ y ∈ W, y ∈ S}`, plus left invariance of `μ`.
- `measure_inter_translate_le`: a pointwise comparison of the integrands `ν (W ∩ x⁻¹ S)` and
  `ν (x W ∩ S)`, up to the factor `η` from the approximate-invariance hypothesis. It assumes
  `O O⁻¹ ⊆ N`, `1 ∈ O`, `W ⊆ O` and `S ⊆ O`. Write `R = W ∩ x⁻¹ S`, so that `x W ∩ S = x R`.
  If `R` is empty, both sides vanish. Otherwise `x` and `x⁻¹` lie in `O O⁻¹ ⊆ N`, and the
  hypothesis applies to translation by `x` on `R` and by `x⁻¹` on `x R`.
- `modularCharacter_le_of_comparison_aux`: the bound `modularCharacter g ≤ (1 + η)^3 D` for a
  fixed `η`.

## Proof of the fixed-`η` bound

Fix a left Haar measure `μ`. Let `N` come from `happrox`.

1. Choose an open `O ∋ 1` with `O O⁻¹ ⊆ N`: take `O₀` with `O₀ O₀ ⊆ N`
   (`exists_open_nhds_one_mul_subset`) and set `O = O₀ ∩ O₀⁻¹`. Choose a compact neighbourhood
   `K` of `1` and set `W = O ∩ interior K`.
2. The convolution `F = μ ∗ₘ ν.restrict W` is left-invariant and finite on compacts. Since `H`
   is second countable, `F = c • μ` with `c = haarScalarFactor F μ`
   (`isMulLeftInvariant_eq_smul`).
3. Let `a = μ W⁻¹`, which is nonzero and finite. For measurable `S ⊆ O`, integrate the pointwise
   comparison. With `mconv_restrict_apply` and `lintegral_measure_translate_inter` this gives
   `c μ S ≤ (1 + η) a ν S` and `a ν S ≤ (1 + η) c μ S`. The case `S = W`, together with `hpos`,
   shows `c ≠ 0`.
4. Apply `hdet` to the neighbourhood `W ∩ {x | g x g⁻¹ ∈ O}` of `1`. This gives an open `V ∋ 1`
   with `V ⊆ W` and `g V g⁻¹ ⊆ O`, so `μ V` is nonzero and finite. Then
   `c Δ(g) μ V = c μ (g V g⁻¹) ≤ (1 + η) a ν (g V g⁻¹) ≤ (1 + η)^2 D a ν V ≤ (1 + η)^3 D c μ V`.
   Cancelling `c μ V` gives the bound.

The main theorem follows by letting `η → 0⁺`. The bound `(1 + η)^3 D` is continuous in `η` and
tends to `D` (`ge_of_tendsto` along `𝓝[>] 0`).

## Provenance

This is a standard argument, written for this project. It compares the Haar measure with a
locally almost-invariant measure by convolving and then using uniqueness of Haar measure. The
module cites no literature statement. It is an internal step toward the Library statement
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`. The Lean
proof uses only Mathlib's convolution `Measure.mconv`, uniqueness of Haar measure in
second-countable groups, and Fubini. It uses no invariant differential forms.
