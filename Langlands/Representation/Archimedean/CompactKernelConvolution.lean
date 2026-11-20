import Langlands.Representation.Archimedean.SmoothOrbitAveraging
import Langlands.Analysis.CompactManifoldWeightedIntegralProof
import Mathlib.MeasureTheory.Integral.Prod

/-! # Smoothing after a compactly parametrized orbit average -/

noncomputable section

open MeasureTheory Set Topology
open scoped Manifold ContDiff Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors (smoothedOperator smoothedOperator_apply)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  (j : C(X, Aˣ)) (w : C(X, ℂ))

local notation "I" => 𝓘(ℝ, A)

/-- Average left translates of a scalar kernel over a compact parameter measure. -/
def compactKernelConvolution (κ : Aˣ → ℂ) (g : Aˣ) : ℂ :=
  ∫ x, κ (j x * g) • w x ∂ν

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [IsFiniteMeasure ν]
  [NormedAlgebra ℝ A] [CompleteSpace A] in
private theorem mem_compactKernelSupport {κ : Aˣ → ℂ} {x : X} {g : Aˣ}
    (h : κ (j x * g) ≠ 0) : g ∈ (Set.range j)⁻¹ * tsupport κ := by
  refine Set.mem_mul.mpr ⟨(j x)⁻¹, Set.inv_mem_inv.mpr ⟨x, rfl⟩,
    j x * g, subset_tsupport κ h, ?_⟩
  exact inv_mul_cancel_left _ _

omit [T2Space X] [BorelSpace X] [IsFiniteMeasure ν] [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- A compact family of translates preserves compact support of the integrated kernel. -/
theorem hasCompactSupport_compactKernelConvolution {κ : Aˣ → ℂ} (hk : HasCompactSupport κ) :
    HasCompactSupport (compactKernelConvolution ν j w κ) := by
  apply HasCompactSupport.of_support_subset_isCompact ((isCompact_range j.continuous).inv.mul hk)
  intro g hg
  by_contra h
  apply hg
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro x
  have he : κ (j x * g) = 0 := by
    by_contra ne
    exact h (mem_compactKernelSupport j ne)
  simp [he]

/-- A smooth kernel remains smooth after averaging the compact family of translates. -/
theorem contMDiff_compactKernelConvolution {κ : Aˣ → ℂ}
    (hκ : ContMDiff I 𝓘(ℝ, ℂ) ∞ κ) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (compactKernelConvolution ν j w κ) := by
  have hh : ContMDiff ((I).prod I) 𝓘(ℝ, ℂ) ∞ (fun p : Aˣ × Aˣ => κ (p.2 * p.1)) :=
    hκ.comp (contMDiff_snd.mul contMDiff_fst)
  exact (Langlands.Analysis.compactManifoldWeightedIntegral X A Aˣ A Aˣ ℂ ν w j _ hh).2

variable [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E)) (μ : Measure Aˣ) [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]

/-- Smoothing a compact orbit average equals smoothing the original vector with the compact
convolution kernel. The equality uses actual right invariance of the group measure. -/
theorem smoothedOperator_compactKernelConvolution (hR : IsContinuousRepresentation R)
    {κ : Aˣ → ℂ} (hκ : ContMDiff I 𝓘(ℝ, ℂ) ∞ κ) (hk : HasCompactSupport κ) (v : E) :
    smoothedOperator R μ hR (compactKernelConvolution ν j w κ)
      (contMDiff_compactKernelConvolution ν j w hκ).continuous
      (hasCompactSupport_compactKernelConvolution ν j w hk) v =
    smoothedOperator R μ hR κ hκ.continuous hk (∫ x, w x • R (j x) v ∂ν) := by
  let T := smoothedOperator R μ hR κ hκ.continuous hk
  let f : X → Aˣ → E := fun x g => (κ (j x * g⁻¹) • w x) • R g v
  have hc : Continuous (Function.uncurry f) := by
    have hz : Continuous (fun p : X × Aˣ => κ (j p.1 * p.2⁻¹)) :=
      hκ.continuous.comp ((j.continuous.comp continuous_fst).mul (continuous_inv.comp continuous_snd))
    exact (hz.smul (w.continuous.comp continuous_fst)).smul
      (hR.comp (continuous_snd.prodMk continuous_const))
  have hf : HasCompactSupport (Function.uncurry f) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_univ.prod ((isCompact_range j.continuous).inv.mul hk).inv)
    rintro ⟨x, g⟩ hg
    refine ⟨Set.mem_univ _, ?_⟩
    have hh : κ (j x * g⁻¹) ≠ 0 := fun he => hg (by simp [Function.uncurry, f, he])
    exact Set.mem_inv.mpr (mem_compactKernelSupport j hh)
  have hi : Integrable (fun x => w x • R (j x) v) ν :=
    (w.continuous.smul (hR.comp (j.continuous.prodMk continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ g, compactKernelConvolution ν j w κ g⁻¹ • R g v ∂μ) =
    T (∫ x, w x • R (j x) v ∂ν)
  calc
    _ = ∫ g, (∫ x, f x g ∂ν) ∂μ := by
      congr 1 with g
      change (∫ x, κ (j x * g⁻¹) • w x ∂ν) • R g v =
        ∫ x, (κ (j x * g⁻¹) • w x) • R g v ∂ν
      rw [integral_smul_const]
    _ = ∫ x, (∫ g, f x g ∂μ) ∂ν :=
      (integral_integral_swap_of_hasCompactSupport hc hf).symm
    _ = _ := by
      rw [← T.integral_comp_comm hi]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change (∫ g, f x g ∂μ) = T (w x • R (j x) v)
      rw [map_smul]
      change (∫ g, f x g ∂μ) = w x • ∫ g, κ g⁻¹ • R g (R (j x) v) ∂μ
      rw [← integral_smul, ← integral_mul_right_eq_self (f x) (j x)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro g
      simp only [f, mul_inv_rev, mul_inv_cancel_left, map_mul, mul_apply_eq_comp, smul_smul,
        smul_eq_mul, mul_comm]

end Langlands.Archimedean
