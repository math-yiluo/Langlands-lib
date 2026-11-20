import Langlands.Representation.GodementJacquet.ComplexTriangularZetaWeight
import Langlands.Group.GL.Maps

/-! # Scalar diagonal weights for the inverse-transposed matrix integral -/

noncomputable section

open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "J" => UpperEntryPair n
local notation "D" => I → ℂˣ
local notation "U" => upperUnipotent n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "G" => GeneralLinear n ℂ

private theorem complexNormalizedAbs_inv (z : ℂ) :
    complexNormalizedAbs z⁻¹ = (complexNormalizedAbs z)⁻¹ := by
  rw [complexNormalizedAbs, complexNormalizedAbs, norm_inv, inv_pow]

/-- Inverse transpose negates the determinant exponent. -/
theorem detPower_complex_inverseTranspose {k : ℕ} (g : GeneralLinear k ℂ) (s : ℂ) :
    detPower complexNormalizedAbs (inverseTranspose k ℂ g) s =
      detPower complexNormalizedAbs g (-s) := by
  have hdet : (inverseTranspose k ℂ g).val.det = g.val.det⁻¹ := by
    rw [inverseTranspose_coe, Matrix.det_transpose]
    change ((Matrix.GeneralLinearGroup.det g⁻¹ : ℂˣ) : ℂ) = _
    rw [map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [detPower, detPower, hdet, complexNormalizedAbs_inv, Real.log_inv, Complex.ofReal_neg,
    mul_neg, neg_mul]

private theorem upperEntryColumnJacobian_eq_prod (d : D) :
    ((↑((∏ ij : J, complexAbsHom (d ij.1.2 : ℂ))⁻¹) : ℝ) : ℂ) =
      ∏ i : I, Complex.exp (-(i.val : ℂ) *
        (Real.log (complexNormalizedAbs (d i : ℂ)) : ℂ)) := by
  rw [prod_complexUpperEntryColumnScale, ← Finset.prod_inv_distrib,
    NNReal.coe_prod, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [NNReal.coe_inv, NNReal.coe_pow, Complex.ofReal_inv, coe_complexAbsHom]
  rw [Complex.ofReal_pow, ← Complex.cpow_natCast, ← Complex.cpow_neg]
  change (↑(complexNormalizedAbs (d i : ℂ)) : ℂ) ^ (-(i.val : ℂ)) = _
  have hz : 0 < complexNormalizedAbs (d i : ℂ) :=
    pow_pos (norm_pos_iff.mpr (d i).ne_zero) _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne'),
    ← Complex.ofReal_log hz.le, mul_comm]

/-- In the lower triangular expansion the column Jacobian cancels the
inverted Borel half-modulus and the rank shift. -/
theorem complexTriangular_dualZetaWeight (χ : ℕ → ℂˣ → ℂ)
    (d : D) (u : U) (k : K) (s : ℂ) :
    ((↑((∏ ij : J, complexAbsHom (d ij.1.2 : ℂ))⁻¹) : ℝ) : ℂ) *
      principalSeriesCharacter ℂ n χ d⁻¹ *
        detPower complexNormalizedAbs
          (inverseTranspose n ℂ (diagonalMatrixUnits ℂ d⁻¹ * u.val * k.val))
          (s + (r : ℂ) / 2) =
      complexDiagonalZetaWeight (fun i z => χ i z⁻¹) d s := by
  rw [upperEntryColumnJacobian_eq_prod, principalSeriesCharacter, detPower_complex_inverseTranspose,
    detPower_diagonal_unipotent_unitary, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  unfold complexDiagonalZetaWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.finrank_real_complex]
  have hz : 0 < complexNormalizedAbs ((d i)⁻¹ : ℂˣ) :=
    pow_pos (norm_pos_iff.mpr ((d i)⁻¹ : ℂˣ).ne_zero) _
  have hpow (v : ℂ) : (↑(complexNormalizedAbs ((d i)⁻¹ : ℂˣ)) : ℂ) ^ v =
      Complex.exp (v * (Real.log (complexNormalizedAbs ((d i)⁻¹ : ℂˣ)) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne'),
      ← Complex.ofReal_log hz.le, mul_comm]
  have hlog : Real.log (complexNormalizedAbs ((d i)⁻¹ : ℂˣ)) =
      - Real.log (complexNormalizedAbs (d i : ℂ)) := by
    rw [Units.val_inv_eq_inv_val, complexNormalizedAbs_inv, Real.log_inv]
  simp only [Pi.inv_apply]
  change Complex.exp (-(i.val : ℂ) * _) *
    (χ i.val (d i)⁻¹ * (↑(complexNormalizedAbs ((d i)⁻¹ : ℂˣ)) : ℂ) ^
      (((↑(r + 1 : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ))) *
      Complex.exp (-(s + (r : ℂ) / 2) *
        (Real.log (complexNormalizedAbs ((d i)⁻¹ : ℂˣ)) : ℂ)) = _
  rw [hpow, hlog, Complex.ofReal_neg]
  let l : ℂ := Real.log (complexNormalizedAbs (d i : ℂ))
  let h : ℂ := ((↑(r + 1 : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ)
  have hsum : -(i.val : ℂ) * l + h * (-l) + (-(s + (r : ℂ) / 2)) * (-l) =
      s * l := by dsimp [h]; push_cast; ring
  calc
    _ = χ i.val (d i)⁻¹ * (Complex.exp (-(i.val : ℂ) * l) * Complex.exp (h * (-l)) *
        Complex.exp (-(s + (r : ℂ) / 2) * (-l))) := by dsimp [h, l]; ring
    _ = _ := by rw [← Complex.exp_add, ← Complex.exp_add, hsum]

end Langlands.GodementJacquet
