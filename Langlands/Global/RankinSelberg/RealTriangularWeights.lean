import Langlands.Global.RankinSelberg.RealTriangularEntries
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Representation.Archimedean.RealJacquetMatrixCoefficient
import Langlands.Group.GL.Maps

/-! # Normalized diagonal weights in the real triangular expansions -/

noncomputable section

open scoped NNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "J" => UpperEntryPair n
local notation "D" => I → ℝˣ
local notation "U" => upperUnipotent n ℝ
local notation "K" => unitaryCompact ℝ n
local notation "G" => GeneralLinear n ℝ

private theorem cpow_of_pos (x : ℝ) (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp (s * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le,
    mul_comm]

/-- The absolute determinant in triangular coordinates. -/
def realDiagonalAbs {m : ℕ} (d : Fin m → ℝˣ) : ℝ := ∏ i, |(d i : ℝ)|

theorem realDiagonalAbs_pos {m : ℕ} (d : Fin m → ℝˣ) : 0 < realDiagonalAbs d :=
  Finset.prod_pos fun i _ => abs_pos.mpr (d i).ne_zero

theorem realDiagonalAbs_inv {m : ℕ} (d : Fin m → ℝˣ) :
    realDiagonalAbs d⁻¹ = (realDiagonalAbs d)⁻¹ := by
  simp only [realDiagonalAbs, Pi.inv_apply, Units.val_inv_eq_inv_val, abs_inv, Finset.prod_inv_distrib]

theorem realNormalizedAbs_det_triangular (d : D) (u : U) (k : K) :
    realNormalizedAbs (diagonalMatrixUnits ℝ d * u.val * k.val : G).val.det = realDiagonalAbs d :=
  (RealJacquetCoefficient.abs_prod_eq_abs_det_of_iwasawa d u k.property).symm

theorem realNormalizedAbs_det_inverseTranspose {m : ℕ} (g : GeneralLinear m ℝ) :
    realNormalizedAbs (inverseTranspose m ℝ g).val.det = (realNormalizedAbs g.val.det)⁻¹ := by
  rw [inverseTranspose_coe, Matrix.det_transpose]
  change |((Matrix.GeneralLinearGroup.det g⁻¹ : ℝˣ) : ℝ)| = |g.val.det|⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, abs_inv]

theorem realNormalizedAbs_det_dualTriangular (d : D) (u : U) (k : K) :
    realNormalizedAbs (inverseTranspose n ℝ (diagonalMatrixUnits ℝ d⁻¹ * u.val * k.val)).val.det =
      realDiagonalAbs d := by
  rw [realNormalizedAbs_det_inverseTranspose, realNormalizedAbs_det_triangular,
    realDiagonalAbs_inv, inv_inv]

/-- The product of the one-dimensional Tate weights on the diagonal. -/
def realDiagonalZetaWeight (χ : ℕ → ℝˣ → ℂ) (d : D) (s : ℂ) : ℂ :=
  ∏ i : I, χ i.val (d i) * Complex.exp (s * (Real.log |(d i : ℝ)| : ℂ))

theorem realDiagonalZetaWeight_eq (χ : ℕ → ℝˣ → ℂ) (d : D) (s : ℂ) :
    realDiagonalZetaWeight χ d s = (∏ i : I, χ i.val (d i)) *
      Complex.exp (s * (Real.log (realDiagonalAbs d) : ℂ)) := by
  rw [realDiagonalZetaWeight, Finset.prod_mul_distrib, realDiagonalAbs,
    Real.log_prod (fun i _ => (abs_pos.mpr (d i).ne_zero).ne'), Complex.ofReal_sum,
    Finset.mul_sum, Complex.exp_sum]

theorem detPower_real_triangular (d : D) (u : U) (k : K) (s : ℂ) :
    detPower realNormalizedAbs (diagonalMatrixUnits ℝ d * u.val * k.val) s =
      ∏ i : I, Complex.exp (s * (Real.log |(d i : ℝ)| : ℂ)) := by
  rw [detPower, realNormalizedAbs_det_triangular, realDiagonalAbs,
    Real.log_prod (fun i _ => (abs_pos.mpr (d i).ne_zero).ne'), Complex.ofReal_sum,
    Finset.mul_sum, Complex.exp_sum]

theorem detPower_real_dualTriangular (d : D) (u : U) (k : K) (s : ℂ) :
    detPower realNormalizedAbs (inverseTranspose n ℝ (diagonalMatrixUnits ℝ d⁻¹ * u.val * k.val)) s =
      ∏ i : I, Complex.exp (s * (Real.log |(d i : ℝ)| : ℂ)) := by
  rw [detPower, realNormalizedAbs_det_dualTriangular, realDiagonalAbs,
    Real.log_prod (fun i _ => (abs_pos.mpr (d i).ne_zero).ne'), Complex.ofReal_sum,
    Finset.mul_sum, Complex.exp_sum]

private theorem entryJacobian_eq_prod (d : D) (m : I → ℕ) :
    ((↑((∏ i : I, ‖(d i : ℝ)‖₊ ^ m i)⁻¹) : ℝ) : ℂ) =
      ∏ i : I, Complex.exp (-(m i : ℂ) * (Real.log |(d i : ℝ)| : ℂ)) := by
  rw [← Finset.prod_inv_distrib, NNReal.coe_prod, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [NNReal.coe_inv, NNReal.coe_pow, Complex.ofReal_inv, coe_nnnorm, Real.norm_eq_abs]
  rw [Complex.ofReal_pow, ← Complex.cpow_natCast, ← Complex.cpow_neg]
  exact cpow_of_pos _ (abs_pos.mpr (d i).ne_zero) _

/-- The row Jacobian cancels the Borel half-modulus and the rank shift. -/
theorem realTriangular_zetaWeight (χ : ℕ → ℝˣ → ℂ) (d : D) (u : U) (k : K) (s : ℂ) :
    ((↑((∏ ij : J, ‖(d ij.1.1 : ℝ)‖₊)⁻¹) : ℝ) : ℂ) *
      principalSeriesCharacter ℝ n χ d *
        detPower realNormalizedAbs (diagonalMatrixUnits ℝ d * u.val * k.val) (s + (r : ℂ) / 2) =
      realDiagonalZetaWeight χ d s := by
  rw [prod_realUpperEntryScale, Nat.add_sub_cancel, entryJacobian_eq_prod,
    principalSeriesCharacter, detPower_real_triangular,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  unfold realDiagonalZetaWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Module.finrank_self, pow_one, Real.norm_eq_abs,
    cpow_of_pos _ (abs_pos.mpr (d i).ne_zero), Nat.cast_sub (Nat.le_of_lt_succ i.isLt)]
  let l : ℂ := Real.log |(d i : ℝ)|
  let h : ℂ := ((↑(r + 1 : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ)
  have hsum : -((r : ℂ) - (i.val : ℂ)) * l + h * l + (s + (r : ℂ) / 2) * l = s * l := by
    dsimp [h]; push_cast; ring
  calc
    _ = χ i.val (d i) * (Complex.exp (-((r : ℂ) - (i.val : ℂ)) * l) *
        Complex.exp (h * l) * Complex.exp ((s + (r : ℂ) / 2) * l)) := by dsimp [h, l]; ring
    _ = _ := by rw [← Complex.exp_add, ← Complex.exp_add, hsum]

/-- The column Jacobian in the dual expansion cancels the inverted Borel half-modulus
and the rank shift. -/
theorem realTriangular_dualZetaWeight (χ : ℕ → ℝˣ → ℂ) (d : D) (u : U) (k : K) (s : ℂ) :
    ((↑((∏ ij : J, ‖(d ij.1.2 : ℝ)‖₊)⁻¹) : ℝ) : ℂ) *
      principalSeriesCharacter ℝ n χ d⁻¹ *
        detPower realNormalizedAbs (inverseTranspose n ℝ (diagonalMatrixUnits ℝ d⁻¹ * u.val * k.val))
          (s + (r : ℂ) / 2) = realDiagonalZetaWeight (fun i z => χ i z⁻¹) d s := by
  rw [prod_realUpperEntryColumnScale, entryJacobian_eq_prod,
    principalSeriesCharacter, detPower_real_dualTriangular,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  unfold realDiagonalZetaWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.inv_apply, Module.finrank_self, pow_one, Real.norm_eq_abs]
  rw [cpow_of_pos _ (abs_pos.mpr ((d i)⁻¹).ne_zero), Units.val_inv_eq_inv_val, abs_inv,
    Real.log_inv, Complex.ofReal_neg]
  let l : ℂ := Real.log |(d i : ℝ)|
  let h : ℂ := ((↑(r + 1 : ℕ) : ℂ) - 1) / 2 - (i.val : ℂ)
  have hsum : -(i.val : ℂ) * l + h * (-l) + (s + (r : ℂ) / 2) * l = s * l := by
    dsimp [h]; push_cast; ring
  calc
    _ = χ i.val (d i)⁻¹ * (Complex.exp (-(i.val : ℂ) * l) *
        Complex.exp (h * (-l)) * Complex.exp ((s + (r : ℂ) / 2) * l)) := by dsimp [h, l]; ring
    _ = _ := by rw [← Complex.exp_add, ← Complex.exp_add, hsum]

/-- The two normalized weight identities used on the full real diagonal torus. -/
def RealTriangularWeightsStatement : Prop :=
  ∀ (χ : ℕ → ℝˣ → ℂ) (d : D) (u : U) (k : K) (s : ℂ),
    ((↑((∏ ij : J, ‖(d ij.1.1 : ℝ)‖₊)⁻¹) : ℝ) : ℂ) *
        principalSeriesCharacter ℝ n χ d *
        detPower realNormalizedAbs (diagonalMatrixUnits ℝ d * u.val * k.val) (s + (r : ℂ) / 2) =
      realDiagonalZetaWeight χ d s ∧
    ((↑((∏ ij : J, ‖(d ij.1.2 : ℝ)‖₊)⁻¹) : ℝ) : ℂ) *
        principalSeriesCharacter ℝ n χ d⁻¹ *
        detPower realNormalizedAbs (inverseTranspose n ℝ (diagonalMatrixUnits ℝ d⁻¹ * u.val * k.val))
          (s + (r : ℂ) / 2) = realDiagonalZetaWeight (fun i z => χ i z⁻¹) d s

theorem realTriangularWeights : RealTriangularWeightsStatement (r := r) :=
  fun χ d u k s => ⟨realTriangular_zetaWeight χ d u k s, realTriangular_dualZetaWeight χ d u k s⟩

end Langlands.GodementJacquet
