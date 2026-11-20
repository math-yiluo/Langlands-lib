import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Distribution.Distribution

/-! # Finite derivative bounds on a fixed compact set -/

noncomputable section

open scoped ContDiff Distributions NNReal
open Set TopologicalSpace

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_compactTestOrder_bound {Ω : Opens E} (T : 𝓓'(Ω, F))
    {K : Compacts E} (hK : (K : Set E) ⊆ Ω) :
    ∃ m : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ f : 𝓓_{K}(E, ℝ), ‖T (TestFunction.ofSupportedIn hK f)‖ ≤
        (C : ℝ) * ContDiffMapSupportedIn.supSeminorm ℝ E ℝ ⊤ K m f := by
  let L : 𝓓_{K}(E, ℝ) →L[ℝ] F :=
    (T : 𝓓(Ω, ℝ) →L[ℝ] F).comp (TestFunction.ofSupportedInCLM ℝ hK)
  let q : Seminorm ℝ 𝓓_{K}(E, ℝ) := (normSeminorm ℝ F).comp L.toLinearMap
  let p := ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K
  obtain ⟨s, C, hC, hq⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) q (continuous_norm.comp L.continuous)
  let m := s.sup id
  have hp : s.sup p ≤ (Finset.Iic m).sup p := by
    apply Finset.sup_mono
    intro j hj
    exact Finset.mem_Iic.mpr (Finset.le_sup (f := id) hj)
  refine ⟨m, C, hC, fun f => ?_⟩
  have h := hq f
  change ‖T (TestFunction.ofSupportedIn hK f)‖ ≤ (C : ℝ) * (s.sup p) f at h
  exact h.trans (mul_le_mul_of_nonneg_left (hp f) C.coe_nonneg)

/-- One derivative order bounding a smooth distribution on tests supported in `K`. -/
def smoothDistributionCompactOrder {Ω : Opens E} (T : 𝓓'(Ω, F))
    {K : Compacts E} (hK : (K : Set E) ⊆ Ω) : ℕ :=
  (exists_compactTestOrder_bound T hK).choose

theorem exists_bound_smoothDistributionCompactOrder {Ω : Opens E} (T : 𝓓'(Ω, F))
    {K : Compacts E} (hK : (K : Set E) ⊆ Ω) :
    ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ f : 𝓓_{K}(E, ℝ), ‖T (TestFunction.ofSupportedIn hK f)‖ ≤
        (C : ℝ) * ContDiffMapSupportedIn.supSeminorm ℝ E ℝ ⊤ K
          (smoothDistributionCompactOrder T hK) f :=
  (exists_compactTestOrder_bound T hK).choose_spec

/-- When the derivatives through order `m` vanish at `a`, a derivative of order `j`
gains one power of the displacement for each further zero order used in the estimate. -/
theorem norm_iteratedFDeriv_le_pow_of_flat {f : E → F} (hf : ContDiff ℝ ∞ f)
    (a : E) (m : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hzero : ∀ j ≤ m, iteratedFDeriv ℝ j f a = 0)
    (hbound : ∀ j ≤ m + 1, ∀ b : E, ‖iteratedFDeriv ℝ j f b‖ ≤ M)
    (r j : ℕ) (hjr : j + r ≤ m + 1) (b : E) :
    ‖iteratedFDeriv ℝ j f b‖ ≤ M * ‖b - a‖ ^ r := by
  induction r generalizing j b with
  | zero =>
      simpa using hbound j (by omega) b
  | succ r ih =>
      let s := Metric.closedBall a ‖b - a‖
      have hd : Differentiable ℝ (iteratedFDeriv ℝ j f) :=
        hf.differentiable_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
      have hbnd (y : E) (hy : y ∈ s) :
          ‖fderiv ℝ (iteratedFDeriv ℝ j f) y‖ ≤ M * ‖b - a‖ ^ r := by
        rw [norm_fderiv_iteratedFDeriv]
        have hy' : ‖y - a‖ ≤ ‖b - a‖ := by
          simpa only [s, Metric.mem_closedBall, dist_eq_norm] using hy
        exact (ih (j + 1) (by omega) y).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy' _) hM)
      have ha : a ∈ s := Metric.mem_closedBall_self (norm_nonneg _)
      have hb : b ∈ s := Metric.mem_closedBall.mpr (by rw [dist_eq_norm])
      have hh := (convex_closedBall a ‖b - a‖).norm_image_sub_le_of_norm_fderiv_le
        (fun y _ => hd y) hbnd ha hb
      rw [hzero j (by omega), sub_zero] at hh
      simpa only [pow_succ, ← mul_assoc] using hh

end Langlands.HarmonicAnalysis
