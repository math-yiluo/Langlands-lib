import Langlands.Analysis.SmoothCompactKernelConvolutionProof
import Langlands.Analysis.SmoothNormalizedInverseKernelProof
import Langlands.Representation.Archimedean.SmoothDerivativeTopology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Group.Units

/-! # Smooth vectors by averaging a Banach representation -/

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E)) (μ : Measure Aˣ)

local notation "𝓜" => 𝓘(ℝ, A)

/-- Apply a kernel to a vector by averaging its orbit against the inverse kernel. -/
def smoothedVector (κ : Aˣ → ℂ) (v : E) : E :=
  ∫ g, κ g⁻¹ • R g v ∂μ

variable [IsFiniteMeasureOnCompacts μ]

private theorem orbit_convolution (hR : IsContinuousRepresentation R)
    {κ : Aˣ → ℂ} (hκ : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ κ) (hc : HasCompactSupport κ) (v : E) :
    (∀ p : Aˣ, Integrable (fun y => κ (y⁻¹ * p) • R y v) μ) ∧
      ContMDiff 𝓜 𝓘(ℝ, E) ∞ (fun p : Aˣ => ∫ y, κ (y⁻¹ * p) • R y v ∂μ) := by
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let w : C(Aˣ, E) := ⟨fun g => R g v, hR.comp (continuous_id.prodMk continuous_const)⟩
  exact Langlands.Analysis.smoothCompactKernelConvolution A Aˣ E μ w κ hκ hc

variable [μ.IsMulLeftInvariant]

/-- Convolving with a smooth compactly supported kernel produces a genuine smooth vector. -/
theorem isSmoothVector_smoothedVector (hR : IsContinuousRepresentation R)
    {κ : Aˣ → ℂ} (hκ : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ κ) (hc : HasCompactSupport κ) (v : E) :
    IsSmoothVector 𝓜 R (smoothedVector R μ κ v) := by
  obtain ⟨hint, hs⟩ := orbit_convolution R μ hR hκ hc v
  have hi : Integrable (fun y : Aˣ => κ y⁻¹ • R y v) μ := by
    simpa only [mul_one] using hint 1
  have h (p : Aˣ) : R p (smoothedVector R μ κ v) =
      ∫ y, κ (y⁻¹ * p) • R y v ∂μ := by
    rw [smoothedVector, ← (R p).integral_comp_comm hi,
      ← integral_mul_left_eq_self (fun y : Aˣ => κ (y⁻¹ * p) • R y v) p]
    apply integral_congr_ae
    filter_upwards with y
    rw [map_smul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, map_mul, mul_apply_eq_comp]
  have he : orbitMap R (smoothedVector R μ κ v) =
      (fun p : Aˣ => ∫ y, κ (y⁻¹ * p) • R y v ∂μ) := funext h
  rw [IsSmoothVector, he]
  exact hs

variable [μ.IsOpenPosMeasure]

include μ in
/-- The genuine smooth vectors are norm dense in the original Banach representation. -/
theorem dense_smoothVectors_units (hR : IsContinuousRepresentation R) :
    Dense (smoothVectors 𝓜 R : Set E) := by
  intro v
  rw [Metric.mem_closure_iff]
  intro ε hε
  let U : Set Aˣ := {g | ‖R g⁻¹ v - v‖ < ε / 2}
  have hU : U ∈ 𝓝 (1 : Aˣ) := by
    have hh : Continuous (fun g : Aˣ => ‖R g⁻¹ v - v‖) :=
      ((hR.comp (continuous_inv.prodMk continuous_const)).sub continuous_const).norm
    apply hh.continuousAt (gt_mem_nhds ?_)
    simp [half_pos hε]
  obtain ⟨κ, hκ, hk, hsupp, hnonneg, -, hκi, hκnorm⟩ :=
    Langlands.Analysis.smoothNormalizedInverseKernel A Aˣ μ U hU
  let f : Aˣ → ℂ := fun g => κ g
  have hf : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ f := Complex.ofRealCLM.contDiff.contMDiff.comp hκ
  have hfc : HasCompactSupport f := hk.comp_left Complex.ofReal_zero
  let w := smoothedVector R μ f v
  refine ⟨w, isSmoothVector_smoothedVector R μ hR hf hfc v, ?_⟩
  have hs (g : Aˣ) : f g⁻¹ • R g v = κ g⁻¹ • R g v :=
    algebraMap_smul ℂ (κ g⁻¹) (R g v)
  have hRint : Integrable (fun g : Aˣ => κ g⁻¹ • R g v) μ := by
    simpa only [mul_one, hs] using (orbit_convolution R μ hR hf hfc v).1 1
  have hw : w = ∫ g, κ g⁻¹ • R g v ∂μ := by
    simp only [w, smoothedVector, hs]
  have hsub : w - v = ∫ g, κ g⁻¹ • (R g v - v) ∂μ := by
    simp only [hw, smul_sub, integral_sub hRint (hκi.smul_const v), integral_smul_const, hκnorm, one_smul]
  have hnorm : ‖w - v‖ ≤ ε / 2 := by
    rw [hsub]
    calc
      _ ≤ ∫ g, κ g⁻¹ * (ε / 2) ∂μ := by
        apply norm_integral_le_of_norm_le (hκi.mul_const (ε / 2))
        filter_upwards with g
        rw [norm_smul, Real.norm_of_nonneg (hnonneg _)]
        by_cases hg : κ g⁻¹ = 0
        · simp [hg]
        · have hgU : g⁻¹ ∈ U := hsupp (subset_tsupport κ hg)
          have hbound : ‖R g v - v‖ < ε / 2 := by simpa [U] using hgU
          exact mul_le_mul_of_nonneg_left hbound.le (hnonneg _)
      _ = ε / 2 := by rw [integral_mul_const, hκnorm, one_mul]
  rw [dist_comm, dist_eq_norm]
  exact hnorm.trans_lt (half_lt_self hε)

end Langlands.Archimedean
