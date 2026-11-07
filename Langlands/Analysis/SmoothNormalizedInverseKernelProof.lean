import Langlands.Analysis.SmoothNormalizedInverseKernelStatement
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section

universe uV uG

namespace Langlands.Analysis

open MeasureTheory
open scoped Topology Manifold ContDiff

/-- Normalize an actual manifold bump by the positive integral of its inverse. -/
theorem smoothNormalizedInverseKernel :
    SmoothNormalizedInverseKernelStatement.{uV, uG} := by
  intro V _ _ _ G _ _ _ _ _ _ _ _ μ _ _ U hU
  obtain ⟨b, -, hbU⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, V)) (1 : G)).mem_iff.mp hU
  let b' : G → ℝ := fun g => b g⁻¹
  have hb'cont : Continuous b' := b.continuous.comp continuous_inv
  have hb'cs : HasCompactSupport b' :=
    b.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)
  have hb'int : Integrable b' μ := hb'cont.integrable_of_hasCompactSupport hb'cs
  have hI : 0 < ∫ g, b' g ∂μ :=
    hb'cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hb'cs
      (fun g => b.nonneg) (x := 1) (by simp [b'])
  let c : ℝ := (∫ g, b' g ∂μ)⁻¹
  have hc : 0 < c := inv_pos.mpr hI
  have hsupp : tsupport (fun g => c * b g) ⊆ tsupport b :=
    tsupport_mul_subset_right
  refine ⟨fun g => c * b g, contMDiff_const.mul b.contMDiff,
    b.hasCompactSupport.of_isClosed_subset isClosed_closure hsupp,
    hsupp.trans hbU, fun g => mul_nonneg hc.le b.nonneg, ?_,
    hb'int.const_mul c, ?_⟩
  · simpa only [b.eq_one, mul_one] using hc
  · change (∫ g, c * b' g ∂μ) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hI.ne'

end Langlands.Analysis
