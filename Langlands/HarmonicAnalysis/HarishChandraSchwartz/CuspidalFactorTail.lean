import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermTail

/-! # Cuspidal cancellation with a height cutoff

The full constant-term tail estimate gives the cuspidal-factor bound
without any compact invariance of the tail or the weights.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U : Subgroup G}
  {hMU : M ≤ Subgroup.normalizer (U : Set G)} {ν : Measure U} {δ : M →* ℝ≥0ˣ}
  {Ξ σ : G → ℝ} {ΞM σM : M → ℝ}

/-- Arbitrary negative powers of a unipotent cutoff in the cuspidal factor.
The inverse conjugation modulus is retained explicitly. -/
def CuspidalFactorTailBound (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (ν : Measure U) (δ : M →* ℝ≥0ˣ) (Γ : Set U) (f : G → ℂ)
    (T : Set M) (t : M → ℝ) (ΞM σM : M → ℝ) : Prop :=
  ∀ d p : ℝ, 0 ≤ p →
    ∃ c : ℝ≥0, ∀ a ∈ T, ∀ m : M,
      ‖cuspidalFactor hMU ν δ Γ f a m‖ₑ ≤
        c * (((δ a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
          ENNReal.ofReal (t a ^ (-p)) *
            ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))

/-- The actual cancellation mechanism in VIII.3.1, abstracted from the
choice of parabolic: full constant-term bounds plus a height cutoff
give rapid tail decay for the normalized cuspidal factor. -/
theorem cuspidalFactorTailBound_of_constantTermEstimate
    (hν : IsConjModulus hMU ν δ)
    (h45 : ConstantTermEstimate ν δ Ξ σ ΞM σM)
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (hprod : SigmaProductBound M U σ)
    {Γ : Set U} (hΓ : MeasurableSet Γ)
    {f : G → ℂ} (hf : ∀ r : ℝ, nu Ξ σ r f < ⊤)
    (hint : ∀ m : M, Integrable (fun u : U => f ((m : G) * u)) ν)
    (hcusp : ∀ m : M, ∫ u : U, f ((m : G) * u) ∂ν = 0)
    {T : Set M} {V : M → Set U} {t : M → ℝ}
    (ht : ∀ a ∈ T, 0 < t a)
    (hVt : ∀ a ∈ T, ∀ u ∈ V a, t a ≤ 1 + σ u)
    (hBV : ∀ a ∈ T, (conjUnipotent hMU a⁻¹ ⁻¹' Γ)ᶜ ⊆ V a) :
    CuspidalFactorTailBound hMU ν δ Γ f T t ΞM σM := by
  intro d p hp
  obtain ⟨d', c, hc⟩ := h45.tail (fun g => (hΞ g).le) hσ hprod d p hp
  let F : ℝ≥0∞ := nu Ξ σ d' f
  have hF : F ≠ ⊤ := (hf d').ne
  refine ⟨(F * c).toNNReal, fun a ha m => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top hF ENNReal.coe_ne_top)]
  have hcancel := hν.enorm_integral_conj_le a m (hint m) (hcusp m) hΓ (hBV a ha)
  have hbound := hc (V a) (t a) (ht a ha) (hVt a ha) m
  have hweight :
      ∫⁻ u, (V a).indicator (fun u : U => ‖f ((m : G) * u)‖ₑ) u ∂ν ≤
        F * ∫⁻ u, (V a).indicator (fun u : U => ENNReal.ofReal
          (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d'))) u ∂ν := by
    rw [← lintegral_const_mul' _ _ hF]
    refine lintegral_mono fun u => ?_
    by_cases hu : u ∈ V a
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      exact enorm_le_nu_mul hΞ hσ f d' _
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
  rw [cuspidalFactor, enorm_nnreal_mul]
  calc
    (NNReal.sqrt (δ m) : ℝ≥0∞) * _ ≤
        (NNReal.sqrt (δ m) : ℝ≥0∞) *
          ((((δ a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
            ∫⁻ u, (V a).indicator (fun u : U => ‖f ((m : G) * u)‖ₑ) u ∂ν) :=
      mul_le_mul_of_nonneg_left hcancel zero_le
    _ ≤ (NNReal.sqrt (δ m) : ℝ≥0∞) *
        ((((δ a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
          (F * ∫⁻ u, (V a).indicator (fun u : U => ENNReal.ofReal
            (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d'))) u ∂ν)) := by
      gcongr
    _ = F * ((((δ a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)) *
        ((NNReal.sqrt (δ m) : ℝ≥0∞) *
          ∫⁻ u, (V a).indicator (fun u : U => ENNReal.ofReal
            (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d'))) u ∂ν) := by ring
    _ ≤ F * ((((δ a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)) *
        (c * ENNReal.ofReal (t a ^ (-p)) *
          ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))) :=
      mul_le_mul_of_nonneg_left hbound zero_le
    _ = _ := by ring

end Langlands.HarishChandraSchwartz
