import Langlands.Representation.GodementJacquet.ComplexDiagonalHaar
import Langlands.Representation.GodementJacquet.ComplexDiagonalZeta
import Langlands.Representation.GodementJacquet.ComplexTriangularZetaWeight
import Langlands.LocalFactor.ArchimedeanAttachment

/-! # Matching the diagonal group weights to the product Tate kernel -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

variable {r : ℕ}
local notation "I" => Fin (r + 1)
local notation "D" => I → ℂˣ
local notation "Z" => I → ℂ

local instance diagonalWeightTransportUnitsMeasurable : MeasurableSpace ℂˣ := borel _
local instance diagonalWeightTransportUnitsBorel : BorelSpace ℂˣ := ⟨rfl⟩

private theorem exp_normalizedAbs_eq_cpow {z : ℂ} (hz : z ≠ 0) (s : ℂ) :
    Complex.exp (s * (Real.log (complexNormalizedAbs z) : ℂ)) = (‖z‖ : ℂ) ^ (2 * s) := by
  have h₀ : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [complexNormalizedAbs, Real.log_pow, Complex.ofReal_mul,
    Complex.cpow_def_of_ne_zero h₀, ← Complex.ofReal_log (norm_nonneg z)]
  push_cast
  congr 1
  ring

private theorem scalar_weight_with_density (m : ℤ) (t s : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ((complexAbsHom z : ℝ) : ℂ) * complexMellinWeight m (s + t) z =
      ((z / (‖z‖ : ℂ)) ^ m * (‖z‖ : ℂ) ^ (2 * t)) *
        Complex.exp (s * (Real.log (complexNormalizedAbs z) : ℂ)) := by
  have h₀ : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [coe_complexAbsHom, Complex.ofReal_pow, complexMellinWeight, ite_eq_right hz,
    exp_normalizedAbs_eq_cpow hz, ← Complex.cpow_natCast]
  rw [mul_left_comm, ← Complex.cpow_add _ _ h₀, mul_assoc, ← Complex.cpow_add _ _ h₀]
  congr 2
  push_cast
  ring

private theorem haarWeightedKernel_eq (χ : ℕ → ℂˣ → ℂ) (m : I → ℤ) (t : Z)
    (hχ : ∀ (i : I) (z : ℂˣ), χ i.val z =
      ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ m i * (‖(z : ℂ)‖ : ℂ) ^ (2 * t i))
    (Φ : Z → ℂ) (d : D) (s : ℂ) :
    ((complexCoordinateJacobian (complexDiagonalVal d) : ℝ) : ℂ) *
      complexDiagonalZetaKernel Φ m (fun i => s + t i) (complexDiagonalVal d) =
        complexDiagonalZetaWeight χ d s * Φ (complexDiagonalVal d) := by
  simp only [complexDiagonalZetaKernel, complexCoordinateJacobian, NNReal.coe_prod,
    Complex.ofReal_prod, mul_left_comm, ← Finset.prod_mul_distrib, complexDiagonalZetaWeight]
  rw [mul_comm (∏ i, χ i.val (d i) *
    Complex.exp (s * (Real.log (complexNormalizedAbs (d i : ℂ)) : ℂ)))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hχ]
  exact scalar_weight_with_density (m i) (t i) s (d i).ne_zero

/-- The torus integral with a diagonal inducing weight is the corresponding
product Tate integral on its initial domain. -/
theorem integral_complexDiagonalZetaWeight (a : ℂˣ) (χ : ℕ → ℂˣ → ℂ) (m : I → ℤ) (t : Z)
    (hχ : ∀ (i : I) (z : ℂˣ), χ i.val z =
      ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ m i * (‖(z : ℂ)‖ : ℂ) ^ (2 * t i))
    (Φ : SchwartzMap Z ℂ) (s : ℂ) (hs : ∀ i, 0 < (s + t i).re) :
    (∫ d : D, complexDiagonalZetaWeight χ d s * Φ (complexDiagonalVal d) ∂complexDiagonalHaar a) =
      complexDiagonalZeta a Φ m (fun i => s + t i) := by
  let K := complexDiagonalZetaKernel Φ m (fun i => s + t i)
  let F (z : Z) := ((complexCoordinateJacobian z : ℝ) : ℂ) * K z
  have hW : Measurable (fun z : Z => (complexCoordinateJacobian z)⁻¹) :=
    (Finset.measurable_prod _ fun i _ =>
      continuous_complexAbsHom.measurable.comp (measurable_pi_apply i)).inv
  simp_rw [← haarWeightedKernel_eq χ m t hχ Φ _ s]
  change (∫ d : D, F (complexDiagonalVal d) ∂complexDiagonalHaar a) = _
  rw [← measurableEmbedding_complexDiagonalVal.integral_map, complexDiagonalHaar_map,
    integral_withDensity_eq_integral_smul hW, complexDiagonalZeta_eq_integral a Φ m hs]
  apply integral_congr_ae
  filter_upwards [ae_complexCoordinate_ne_zero (ι := I) a] with z hz
  have h₀ : ((complexCoordinateJacobian z : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast complexCoordinateJacobian_ne_zero hz
  simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_inv, Complex.ofReal_inv, F, K,
    ← mul_assoc, inv_mul_cancel₀ h₀, one_mul]

/-- Inverting an inducing character negates its angular integer and its exponent. -/
theorem complexCharacterData_inv_polar (d : ComplexCharacterData) (z : ℂˣ) :
    (d.character z⁻¹ : ℂ) =
      ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (-d.weight) * (‖(z : ℂ)‖ : ℂ) ^ (2 * -d.exponent) := by
  rw [map_inv, Units.val_inv_eq_inv_val, d.character_eq, mul_inv, zpow_neg,
    show 2 * -d.exponent = -(2 * d.exponent) by ring, Complex.cpow_neg]

end Langlands.GodementJacquet
