# Weighted left averages over compact subgroups and their duality

Module `Langlands.Analysis.CompactSubgroupAverageDuality`, namespace
`Langlands.Analysis.CompactAverage`.

## Setting

`H` is a topological group that is Hausdorff, locally compact and second countable, with its
Borel σ-algebra. `C` is a subgroup of `H` that is compact for the subspace topology
(`CompactSpace C`). `ν` is a finite measure on `C`. The module defines no new mathematical object
beyond the average below, and every result is internal: it records standard facts about
convolution over a compact group in the form needed by
`Langlands.Global.RightTranslationTestFunctionSeparationProof`.

## Definitions

| Declaration | Meaning |
| --- | --- |
| `weightedAverage ν a ψ` | `h ↦ ∫_C a(c) ψ(c⁻¹ h) dν(c)` for `a : C → ℂ` and `ψ : H → ℂ` (a Bochner integral, `0` if the integrand is not integrable) |
| `weightLinearMap ν hψ` | for continuous `ψ`, the `ℂ`-linear map `C(C, ℂ) → C(H, ℂ)`, `a ↦ weightedAverage ν a ψ` |
| `averageLinearMap ν` | the `ℂ`-linear map `C(H, ℂ) → (H → ℂ)`, `ψ ↦ weightedAverage ν 1 ψ` |

## Results

- `isCompact_subgroup`: `C` is a compact subset of `H`.
- `integrable_of_continuous`: a continuous function on `C` with values in a normed group is
  `ν`-integrable. The proof restricts to the compact set `univ`, which has finite measure.
- `continuous_weightedAverage`: for continuous `a` and `ψ` the average is continuous. The
  integrand `(h, c) ↦ a(c) ψ(c⁻¹ h)` is jointly continuous and `C` is compact, so Mathlib's
  `continuous_parametric_integral_of_continuous` applies.
- `continuous_integral_mul_left`: for continuous `a` and `Φ`, the function
  `h ↦ ∫_C a(c) Φ(c h) dν(c)` is continuous, by the same lemma.
- `weightedAverage_eq_zero_of_notMem` and `hasCompactSupport_weightedAverage`: the average
  vanishes outside the compact set `C · tsupport ψ`, so it has compact support when `ψ` has.
- `weightedAverage_mul_left`: if `ν` is left invariant, then for `c₀ ∈ C`,
  `weightedAverage ν a ψ (c₀ h) = weightedAverage ν (c ↦ a (c₀ c)) ψ h`. The proof substitutes
  `c ↦ c₀ c` (`integral_mul_left_eq_self`) and uses `(c₀ c)⁻¹ c₀ h = c⁻¹ h`.
- `weightedAverage_mul_left_of_commute`: if `z ∈ H` commutes with every element of `C`, then
  `weightedAverage ν a ψ (z h) = weightedAverage ν a (x ↦ ψ (z x)) h`, because
  `c⁻¹ z h = z c⁻¹ h`.
- `weightLinearMap` and `averageLinearMap` are linear because the integrands involved are
  continuous on the compact group `C`, hence integrable, so the integral is additive and
  homogeneous on them.
- `integral_conj_weightedAverage_mul` (duality): let `μ` be a left-invariant measure on `H` that
  is finite on compact sets and s-finite. Let `a` and `Φ` be continuous, and let `ψ` be
  continuous with compact support. Then
  `∫_H conj (weightedAverage ν a ψ h) · Φ(h) dμ(h) = ∫_H conj ψ(h) · (∫_C conj a(c) · Φ(c h) dν(c)) dμ(h)`.
  The proof first writes the conjugate of the average as an integral over `C`
  (`integral_conj`, `integral_mul_const`). It then swaps the integrals with
  `integral_integral_swap`. The integrand is continuous on `H × C` with support in
  `(C · tsupport ψ) × C`, so it is integrable for `μ.prod ν`
  (`Continuous.integrable_of_hasCompactSupport`). Next it substitutes `h ↦ c h` in the inner
  `H`-integral, using the left invariance of `μ`. Finally it swaps back, the new integrand
  having support in `tsupport ψ × C`.
- `continuous_integral_conj_mul`: for `Ξ ∈ C(C, ℂ)`, the functional
  `w ↦ ∫_C conj w(c) · Ξ(c) dν(c)` on `C(C, ℂ)` with its sup norm is Lipschitz, with constant
  `‖Ξ‖ · ν(C)`. Indeed `‖∫ conj (w − w') Ξ‖ ≤ ‖w − w'‖ ‖Ξ‖ ν(C)` by
  `norm_integral_le_of_norm_le_const`.
- `eq_zero_of_integral_conj_mul_self`: if `ν` is positive on nonempty open sets and
  `∫_C conj Ξ · Ξ dν = 0` for a continuous `Ξ`, then `Ξ = 0`. Here `conj z · z = ‖z‖²`
  (`Complex.conj_mul'`), so the real integral of the continuous nonnegative function `‖Ξ‖²`
  vanishes. It is therefore almost everywhere zero (`integral_eq_zero_iff_of_nonneg`), hence
  zero everywhere by continuity (`Continuous.ae_eq_iff_eq`).

## Provenance

These are the usual properties of left convolution `a * ψ` over a compact group. The duality is
the adjointness of left convolution for the `L²` pairing, together with the left invariance of
the Haar measure. Compare G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC
Press 2015 (`folland-2015-abstract-harmonic-analysis-second`), §2.5 on convolutions on locally
compact groups. The statements are internal and are proved here from Mathlib's Bochner integral,
Fubini theorem and invariant-measure API; no statement is taken verbatim from the source.
