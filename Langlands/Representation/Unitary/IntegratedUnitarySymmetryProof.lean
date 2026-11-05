import Langlands.Representation.Unitary.IntegratedUnitarySymmetryStatement

noncomputable section

namespace Langlands.Analysis

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

universe uG uE

/-- The actual inversion-density formula gives symmetry of the integrated action. -/
theorem integratedUnitarySymmetry : IntegratedUnitarySymmetryStatement.{uG, uE} := by
  intro G _ _ _ E _ _ _ μ π hπinner hπmeas d hd hμ f hf hweight
  let hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖ :=
    fun g => (LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπinner g)
  change (integratedIsometricAction μ π hπnorm hπmeas f hf).IsSymmetric
  intro x y
  have hx := isometricActionIntegrand_integrable μ π hπnorm hπmeas f hf x
  have hy := isometricActionIntegrand_integrable μ π hπnorm hπmeas f hf y
  have hinv (g : G) : inner ℂ (π g x) y = inner ℂ x (π g⁻¹ y) := by
    have hcancel : π g (π g⁻¹ y) = y := by
      change (π g * π g⁻¹) y = y
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    simpa only [hcancel] using hπinner g x (π g⁻¹ y)
  change inner ℂ (∫ g, f g • π g x ∂μ) y =
    inner ℂ x (∫ g, f g • π g y ∂μ)
  calc
    _ = conj (inner ℂ y (∫ g, f g • π g x ∂μ)) := (inner_conj_symm _ _).symm
    _ = conj (∫ g, inner ℂ y (f g • π g x) ∂μ) :=
      congrArg conj (integral_inner hx y).symm
    _ = ∫ g, conj (inner ℂ y (f g • π g x)) ∂μ := integral_conj.symm
    _ = ∫ g, star (f g) * inner ℂ x (π g⁻¹ y) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun g => by
        change conj (inner ℂ y (f g • π g x)) =
          star (f g) * inner ℂ x (π g⁻¹ y)
        rw [inner_conj_symm, inner_smul_left, hinv]
        rfl)
    _ = ∫ g, star (f g⁻¹) * inner ℂ x (π g y) ∂μ.inv := by
      simpa only [Measure.inv_def, MeasurableEquiv.inv_apply, inv_inv] using
        (integral_map_equiv (μ := μ) (MeasurableEquiv.inv G)
          (fun g => star (f g⁻¹) * inner ℂ x (π g y))).symm
    _ = ∫ g, d g • (star (f g⁻¹) * inner ℂ x (π g y)) ∂μ := by
      rw [hμ, integral_withDensity_eq_integral_smul hd]
    _ = ∫ g, f g * inner ℂ x (π g y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hweight] with g hg
      change (d g : ℂ) * (star (f g⁻¹) * inner ℂ x (π g y)) = _
      rw [← mul_assoc, ← hg]
    _ = ∫ g, inner ℂ x (f g • π g y) ∂μ := by
      simp_rw [inner_smul_right]
    _ = inner ℂ x (∫ g, f g • π g y ∂μ) := integral_inner hy x

end Langlands.Analysis
