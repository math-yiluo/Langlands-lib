import Langlands.Representation.GodementJacquet.ComplexTriangularMatrixEntries
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Representation.Archimedean.ComplexMaximalParabolicIntegration

/-! # The rank shift and the additive Jacobian cancel at each diagonal coordinate -/

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
local notation "U" => upperUnipotent n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "G" => GeneralLinear n ℂ

private theorem cpow_of_pos (x : ℝ) (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp (s * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le,
    mul_comm]

private theorem normalizedAbs_unit_pos (z : ℂˣ) : 0 < complexNormalizedAbs (z : ℂ) :=
  pow_pos (norm_pos_iff.mpr z.ne_zero) _

/-- After removing the unipotent row scaling, the determinant twist on the
triangular factor separates as one scalar Tate twist per inducing character. -/
def complexDiagonalZetaWeight (χ : ℕ → ℂˣ → ℂ) (d : I → ℂˣ) (s : ℂ) : ℂ :=
  ∏ i : I, χ i.val (d i) *
    Complex.exp (s * (Real.log (complexNormalizedAbs (d i : ℂ)) : ℂ))

theorem detPower_diagonal_unipotent_unitary (d : I → ℂˣ) (u : U) (k : K) (s : ℂ) :
    detPower complexNormalizedAbs (diagonalMatrixUnits ℂ d * u.val * k.val) s =
      ∏ i : I, Complex.exp (s * (Real.log (complexNormalizedAbs (d i : ℂ)) : ℂ)) := by
  have hk₀ := ComplexMaximalParabolicIntegration.normSqC_det_unitary k
  have hk : complexNormalizedAbs k.val.val.det = (1 : ℝ) := by
    change ((complexNormalizedAbs k.val.val.det : ℝ) : ℂ) = 1 at hk₀
    exact_mod_cast hk₀
  have hd : complexNormalizedAbs (diagonalMatrixUnits ℂ d * u.val * k.val : G).val.det =
      ∏ i : I, complexNormalizedAbs (d i : ℂ) := by
    simp only [Units.val_mul, Matrix.det_mul, Langlands.RankinSelberg.unipotent_det, mul_one,
      diagonalMatrixUnits_val, Matrix.det_diagonal]
    change (complexAbsHom ((∏ i : I, (d i : ℂ)) * k.val.val.det) : ℝ) = _
    rw [map_mul, map_prod, NNReal.coe_mul, NNReal.coe_prod]
    change _ * complexNormalizedAbs k.val.val.det = _
    rw [hk, mul_one]
    rfl
  rw [detPower, hd, Real.log_prod (fun i _ => (normalizedAbs_unit_pos (d i)).ne'),
    Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

private theorem upperEntryJacobian_eq_prod (d : I → ℂˣ) :
    ((↑((∏ ij : J, complexAbsHom (d ij.1.1 : ℂ))⁻¹) : ℝ) : ℂ) =
      ∏ i : I, Complex.exp (-(↑(r - i.val : ℕ) : ℂ) *
        (Real.log (complexNormalizedAbs (d i : ℂ)) : ℂ)) := by
  rw [prod_complexUpperEntryScale, Nat.add_sub_cancel, ← Finset.prod_inv_distrib,
    NNReal.coe_prod, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [NNReal.coe_inv, NNReal.coe_pow, Complex.ofReal_inv, coe_complexAbsHom]
  rw [Complex.ofReal_pow, ← Complex.cpow_natCast, ← Complex.cpow_neg]
  exact cpow_of_pos _ (normalizedAbs_unit_pos (d i)) _

/-- The shift `(n - 1) / 2`, the square root of the upper Borel modulus,
and the additive upper-entry Jacobian give exponent `s` at each diagonal. -/
theorem complexTriangular_zetaWeight (χ : ℕ → ℂˣ → ℂ) (d : I → ℂˣ) (u : U) (k : K) (s : ℂ) :
    ((↑((∏ ij : J, complexAbsHom (d ij.1.1 : ℂ))⁻¹) : ℝ) : ℂ) *
      principalSeriesCharacter ℂ n χ d *
        detPower complexNormalizedAbs (diagonalMatrixUnits ℂ d * u.val * k.val) (s + (r : ℂ) / 2) =
      complexDiagonalZetaWeight χ d s := by
  rw [upperEntryJacobian_eq_prod, principalSeriesCharacter, detPower_diagonal_unipotent_unitary,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  unfold complexDiagonalZetaWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.finrank_real_complex]
  change Complex.exp (-(↑(r - i.val : ℕ) : ℂ) * _) *
    (χ i.val (d i) * ((complexNormalizedAbs (d i : ℂ) : ℝ) : ℂ) ^
      (((↑(r + 1 : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ))) * Complex.exp ((s + (r : ℂ) / 2) * _) = _
  rw [cpow_of_pos _ (normalizedAbs_unit_pos (d i)), Nat.cast_sub (Nat.le_of_lt_succ i.isLt)]
  let l : ℂ := Real.log (complexNormalizedAbs (d i : ℂ))
  have hsum : -((r : ℂ) - (i.val : ℂ)) * l +
      (((↑(r + 1 : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ)) * l + (s + (r : ℂ) / 2) * l =
        s * l := by push_cast; ring
  calc
    _ = χ i.val (d i) * (Complex.exp (-((r : ℂ) - (i.val : ℂ)) * l) *
        Complex.exp ((((↑(r + 1 : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ)) * l) *
        Complex.exp ((s + (r : ℂ) / 2) * l)) := by dsimp [l]; ring
    _ = _ := by rw [← Complex.exp_add, ← Complex.exp_add, hsum]

end Langlands.GodementJacquet
