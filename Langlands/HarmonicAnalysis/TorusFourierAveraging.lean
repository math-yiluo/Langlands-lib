import Langlands.HarmonicAnalysis.TorusFourierDecay

/-! # Averaging over a torus of twists: the first bound in the proof of Prop. VI.3.1

Let `T` be a group with a left invariant finite measure `μ` (Waldspurger's `Im X(M)`), let
`ι : (J → Circle) → T` be continuous (the torus `Im X(G)` in coordinates, mapped to `T`), and let
`ν` be a finite measure on `J → Circle`. For `n : J → ℤ` (the coordinates of `H_G(g)`) and
`φ : T → ℂ`, `torusAverage ν ι φ n χ = ∫ φ(ι(z) χ) zⁿ dν(z)` is the analogue of Waldspurger's
`φ_g(χ) = ∫_{Im X(G)} φ(λχ) λ(g) dλ`. Waldspurger's measure `dλ` (I.1) has total mass
`d_G = |ker(Im X(G) → Im X(A_G))|`, which need not be `1`; for a probability measure `ν`,
`torusAverage` is `d_G⁻¹` times the printed average.

If `F : T → ℂ` is continuous with `F(ι(z) χ) = zⁿ F(χ)` (as `χ ↦ E_P^G sp_χ ψ (g)`), then
`∫_T φ_g F dμ = ν(J → Circle) ∫_T φ F dμ`; for probability `ν` this is `∫_T φ F dμ`. With the
rapid decay of Fourier coefficients (`norm_torusFourierCoeff_le_rpow`) and a bound `|F| ≤ B`
(Lemma VI.2.2, `B = c Ξ(g)`), this gives
`|∫_T φ F dμ| ≤ 2^k (1 + |J|) M μ(T) B (1 + ‖n‖)^{-r}`, where `M` bounds `φ` and its `k`-th
derivatives along the directions of `ι`.
-/

noncomputable section

open MeasureTheory Complex
open Langlands.Plancherel (IsSmoothFiniteTorusFunction)

namespace Langlands.HarmonicAnalysis.TorusFourier

variable {J : Type*} [Fintype J] {T : Type*} [Group T]

/-- The average `∫ φ(ι(z) χ) zⁿ dν(z)`: the Fourier coefficient at `n` of `z ↦ φ(ι(z) χ)`.
In coordinates, Waldspurger's `φ_g(χ) = ∫_{Im X(G)} φ(λχ) λ(g) dλ` when `ν` is his measure `dλ`
of total mass `d_G`; for the probability Haar measure it is `d_G⁻¹ φ_g(χ)`. -/
def torusAverage (ν : Measure (J → Circle)) (ι : (J → Circle) → T) (φ : T → ℂ) (n : J → ℤ)
    (χ : T) : ℂ :=
  torusFourierCoeff ν (fun z => φ (ι z * χ)) n

theorem torusAverage_apply (ν : Measure (J → Circle)) (ι : (J → Circle) → T) (φ : T → ℂ)
    (n : J → ℤ) (χ : T) :
    torusAverage ν ι φ n χ = ∫ z, φ (ι z * χ) * torusCharacter n z ∂ν :=
  rfl

variable [TopologicalSpace T] [IsTopologicalGroup T] [MeasurableSpace T] [BorelSpace T]

/-- The averaging identity in the proof of Prop. VI.3.1 for a finite measure `ν`:
`∫_T φ_g(χ) F(χ) dμ = ν(J → Circle) ∫_T φ(χ) F(χ) dμ` when `F(ι(z) χ) = zⁿ F(χ)`. -/
theorem integral_torusAverage_mul [CompactSpace T] (μ : Measure T)
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (ν : Measure (J → Circle))
    [IsFiniteMeasure ν] {ι : (J → Circle) → T} (hι : Continuous ι) {φ F : T → ℂ}
    (hφ : Continuous φ) (hF : Continuous F) {n : J → ℤ}
    (hFn : ∀ z χ, F (ι z * χ) = torusCharacter n z * F χ) :
    ∫ χ, torusAverage ν ι φ n χ * F χ ∂μ = ν.real Set.univ • ∫ χ, φ χ * F χ ∂μ := by
  have hcont : Continuous (Function.uncurry fun (z : J → Circle) (χ : T) =>
      φ (ι z * χ) * torusCharacter n z * F χ) :=
    ((hφ.comp ((hι.comp continuous_fst).mul continuous_snd)).mul
      ((continuous_torusCharacter n).comp continuous_fst)).mul (hF.comp continuous_snd)
  have hint : Integrable (Function.uncurry fun (z : J → Circle) (χ : T) =>
      φ (ι z * χ) * torusCharacter n z * F χ) (ν.prod μ) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  symm
  calc ν.real Set.univ • ∫ χ, φ χ * F χ ∂μ
      = ∫ _z, ∫ χ, φ χ * F χ ∂μ ∂ν := by
        rw [integral_const]
    _ = ∫ z, ∫ χ, φ (ι z * χ) * torusCharacter n z * F χ ∂μ ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        rw [← integral_mul_left_eq_self (fun χ => φ χ * F χ) (ι z)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun χ => ?_)
        simp only [hFn, mul_assoc]
    _ = ∫ χ, ∫ z, φ (ι z * χ) * torusCharacter n z * F χ ∂ν ∂μ :=
        integral_integral_swap hint
    _ = ∫ χ, torusAverage ν ι φ n χ * F χ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun χ => ?_)
        dsimp only
        rw [torusAverage_apply, integral_mul_const]

/-- The averaging identity for a probability measure `ν`:
`∫_T φ(χ) F(χ) dμ = ∫_T φ_g(χ) F(χ) dμ` when `F(ι(z) χ) = zⁿ F(χ)`. -/
theorem integral_mul_eq_integral_torusAverage_mul [CompactSpace T] (μ : Measure T)
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (ν : Measure (J → Circle))
    [IsProbabilityMeasure ν] {ι : (J → Circle) → T} (hι : Continuous ι) {φ F : T → ℂ}
    (hφ : Continuous φ) (hF : Continuous F) {n : J → ℤ}
    (hFn : ∀ z χ, F (ι z * χ) = torusCharacter n z * F χ) :
    ∫ χ, φ χ * F χ ∂μ = ∫ χ, torusAverage ν ι φ n χ * F χ ∂μ := by
  rw [integral_torusAverage_mul μ ν hι hφ hF hFn, probReal_univ, one_smul]

variable [DecidableEq J]

omit [TopologicalSpace T] [IsTopologicalGroup T] [MeasurableSpace T] [BorelSpace T] in
/-- Estimate (4) of the proof of Prop. VI.3.1 for `φ_g`: if `z ↦ φ(ι(z) χ)` is smooth for every
`χ` and it and its `k`-th partial derivatives are bounded by `M`, then
`|φ_g(χ)| ≤ 2^k (1 + |J|) M ν(J → Circle) (1 + ‖n‖)^{-r}` for `r ≤ k`. -/
theorem norm_torusAverage_le_rpow (ν : Measure (J → Circle)) [IsFiniteMeasure ν]
    [ν.IsMulLeftInvariant] {ι : (J → Circle) → T} {φ : T → ℂ}
    (hφ : ∀ χ, IsSmoothFiniteTorusFunction fun z => φ (ι z * χ)) {k : ℕ} {r : ℝ} (hr : r ≤ k)
    {M : ℝ} (hM0 : ∀ χ z, ‖φ (ι z * χ)‖ ≤ M)
    (hM : ∀ χ j z, ‖(torusPartialDeriv j)^[k] (fun z => φ (ι z * χ)) z‖ ≤ M) (n : J → ℤ)
    (χ : T) :
    ‖torusAverage ν ι φ n χ‖ ≤
      2 ^ k * (1 + Fintype.card J) * (M * ν.real Set.univ) * (1 + ‖n‖) ^ (-r) :=
  norm_torusFourierCoeff_le_rpow ν (hφ χ) hr (hM0 χ) (hM χ) n

/-- The first bound in the proof of Prop. VI.3.1, in coordinates: for `F(ι(z) χ) = zⁿ F(χ)` with
`|F| ≤ B`, `|∫_T φ F dμ| ≤ 2^k (1 + |J|) M μ(T) B (1 + ‖n‖)^{-r}`, where `M` bounds `φ` and its
`k`-th derivatives along the directions of `ι` and `r ≤ k`. The left invariant probability
measure `ν` is an auxiliary tool and does not occur in the bound. -/
theorem norm_integral_mul_le_rpow [CompactSpace T] (μ : Measure T) [IsFiniteMeasure μ]
    [μ.IsMulLeftInvariant] (ν : Measure (J → Circle)) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] {ι : (J → Circle) → T} (hι : Continuous ι) {φ F : T → ℂ}
    (hφc : Continuous φ) (hφ : ∀ χ, IsSmoothFiniteTorusFunction fun z => φ (ι z * χ))
    (hF : Continuous F) {n : J → ℤ} (hFn : ∀ z χ, F (ι z * χ) = torusCharacter n z * F χ)
    {k : ℕ} {r : ℝ} (hr : r ≤ k) {M B : ℝ} (hM0 : ∀ χ z, ‖φ (ι z * χ)‖ ≤ M)
    (hM : ∀ χ j z, ‖(torusPartialDeriv j)^[k] (fun z => φ (ι z * χ)) z‖ ≤ M)
    (hB : ∀ χ, ‖F χ‖ ≤ B) :
    ‖∫ χ, φ χ * F χ ∂μ‖ ≤
      2 ^ k * (1 + Fintype.card J) * M * μ.real Set.univ * B * (1 + ‖n‖) ^ (-r) := by
  rw [integral_mul_eq_integral_torusAverage_mul μ ν hι hφc hF hFn]
  have hφg : ∀ χ, ‖torusAverage ν ι φ n χ‖ ≤
      2 ^ k * (1 + Fintype.card J) * M * (1 + ‖n‖) ^ (-r) := fun χ => by
    have h := norm_torusAverage_le_rpow ν hφ hr hM0 hM n χ
    rwa [probReal_univ, mul_one] at h
  have hA : ∀ χ, ‖torusAverage ν ι φ n χ * F χ‖ ≤
      2 ^ k * (1 + Fintype.card J) * M * (1 + ‖n‖) ^ (-r) * B := fun χ => by
    rw [norm_mul]
    exact mul_le_mul (hφg χ) (hB χ) (norm_nonneg _) ((norm_nonneg _).trans (hφg χ))
  calc ‖∫ χ, torusAverage ν ι φ n χ * F χ ∂μ‖
      ≤ 2 ^ k * (1 + Fintype.card J) * M * (1 + ‖n‖) ^ (-r) * B * μ.real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hA)
    _ = 2 ^ k * (1 + Fintype.card J) * M * μ.real Set.univ * B * (1 + ‖n‖) ^ (-r) := by ring

end Langlands.HarmonicAnalysis.TorusFourier
