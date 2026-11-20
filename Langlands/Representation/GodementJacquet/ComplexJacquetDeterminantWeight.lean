import Langlands.Representation.GodementJacquet.ComplexRectangularFourierCovariance
import Langlands.Representation.GodementJacquet.ComplexTriangularDualWeight
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

/-! # Determinant weights in the complex Jacquet recursion -/

noncomputable section

open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg.RankOneGammaTwist

variable {n : ℕ}
local notation "G" => GeneralLinear n ℂ
local notation "ι" => inverseTranspose n ℂ

theorem complexNormalizedAbs_det_pos (g : G) :
    0 < complexNormalizedAbs g.val.det :=
  pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) _

theorem detPower_complex_add (g : G) (s t : ℂ) :
    detPower complexNormalizedAbs g (s + t) =
      detPower complexNormalizedAbs g s * detPower complexNormalizedAbs g t := by
  simp only [detPower, add_mul, Complex.exp_add]

theorem detPower_complex_mul (g h : G) (s : ℂ) :
    detPower complexNormalizedAbs (g * h) s =
      detPower complexNormalizedAbs g s * detPower complexNormalizedAbs h s := by
  have hnorm : complexNormalizedAbs (g * h).val.det =
      complexNormalizedAbs g.val.det * complexNormalizedAbs h.val.det := by
    simp only [Units.val_mul, Matrix.det_mul, complexNormalizedAbs, norm_mul, mul_pow]
  rw [detPower, hnorm, Real.log_mul (complexNormalizedAbs_det_pos g).ne'
    (complexNormalizedAbs_det_pos h).ne', Complex.ofReal_add, mul_add, Complex.exp_add]
  rfl

theorem detPower_complex_natCast (g : G) (k : ℕ) :
    detPower complexNormalizedAbs g k = ((complexAbsHom g.val.det ^ k : ℝ≥0) : ℂ) := by
  rw [detPower, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
    ← Real.log_pow, Real.exp_log (pow_pos (complexNormalizedAbs_det_pos g) _)]
  rfl

theorem complexAbsHom_det_weylLong (n : ℕ) :
    complexAbsHom (weylLong n ℂ).val.det = 1 := by
  apply pow_left_injective (by decide : 2 ≠ 0)
  change complexAbsHom (weylLong n ℂ).val.det ^ 2 = 1 ^ (2 : ℕ)
  rw [pow_two, ← map_mul, ← Matrix.det_mul, ← Units.val_mul, weylLong_mul_self]
  simp

theorem detPower_complex_weylLong (n : ℕ) (s : ℂ) :
    detPower complexNormalizedAbs (weylLong n ℂ) s = 1 := by
  have h : complexNormalizedAbs (weylLong n ℂ).val.det = 1 := by
    change (complexAbsHom (weylLong n ℂ).val.det : ℝ) = 1
    rw [complexAbsHom_det_weylLong]
    rfl
  simp [detPower, h]

theorem detPower_complex_inv (g : G) (s : ℂ) :
    detPower complexNormalizedAbs g⁻¹ s = detPower complexNormalizedAbs g (-s) := by
  rw [← detPower_complex_inverseTranspose]
  simp only [detPower, inverseTranspose_coe, Matrix.det_transpose]

/-- A determinant character with an additional normalized absolute-value exponent. -/
def complexJacquetDetWeight (η : ℂˣ →* ℂˣ) (g : G) (s : ℂ) : ℂ :=
  ((η (determinant g) : ℂˣ) : ℂ) * detPower complexNormalizedAbs g s

theorem complexJacquetDetWeight_add (η : ℂˣ →* ℂˣ) (g : G) (s t : ℂ) :
    complexJacquetDetWeight η g (s + t) =
      complexJacquetDetWeight η g s * detPower complexNormalizedAbs g t := by
  simp only [complexJacquetDetWeight, detPower_complex_add, mul_assoc]

theorem complexJacquetDetWeight_mul (η : ℂˣ →* ℂˣ) (g h : G) (s : ℂ) :
    complexJacquetDetWeight η (g * h) s =
      complexJacquetDetWeight η g s * complexJacquetDetWeight η h s := by
  simp only [complexJacquetDetWeight, map_mul, Units.val_mul, detPower_complex_mul]
  ring

theorem complexJacquetDetWeight_inverseTranspose (η : ℂˣ →* ℂˣ) (g : G) (s : ℂ) :
    complexJacquetDetWeight η (ι g) s = complexJacquetDetWeight (η.comp invMonoidHom) g (-s) := by
  rw [complexJacquetDetWeight, determinant_inverseTranspose, detPower_complex_inverseTranspose]
  rfl

theorem complexJacquetDetWeight_weylLong (η : ℂˣ →* ℂˣ) (n : ℕ) (s : ℂ) :
    complexJacquetDetWeight η (weylLong n ℂ) s = ((η (determinant (weylLong n ℂ)) : ℂˣ) : ℂ) := by
  simp [complexJacquetDetWeight, detPower_complex_weylLong]

/-- The product of the two Weyl determinants in adjacent ranks. -/
theorem determinant_weylLong_adjacent (n : ℕ) :
    determinant (weylLong (n + 1) ℂ) * determinant (weylLong n ℂ) = (-1 : ℂˣ) ^ n := by
  rw [determinant_weylLong_succ, mul_assoc, ← map_mul, weylLong_mul_self, map_one, mul_one]

/-- The reciprocal Jacobian for the Jacquet two-sided test with matrices
`k⁻¹` and `g^ι` is the product of the corresponding integer powers. -/
theorem complexRectangularJacobian_jacquet {m : ℕ} (k : GeneralLinear m ℂ) (g : G) :
    ((complexRectangularJacobian k⁻¹ (ι g))⁻¹ : ℝ≥0) =
      detPower complexNormalizedAbs k n * detPower complexNormalizedAbs g m := by
  have hdet (v : GeneralLinear m ℂ) : (v⁻¹).val.det = v.val.det⁻¹ := by
    change ((determinant v⁻¹ : ℂˣ) : ℂ) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    rfl
  have hι : (ι g).val.det = g.val.det⁻¹ := by
    change ((determinant (ι g) : ℂˣ) : ℂ) = _
    rw [determinant_inverseTranspose, Units.val_inv_eq_inv_val]
    rfl
  rw [complexRectangularJacobian, hdet k, hι, map_inv₀, map_inv₀,
    inv_pow, inv_pow, ← mul_inv, inv_inv, detPower_complex_natCast, detPower_complex_natCast]
  simp only [NNReal.coe_mul, Complex.ofReal_mul]

end Langlands.GodementJacquet
