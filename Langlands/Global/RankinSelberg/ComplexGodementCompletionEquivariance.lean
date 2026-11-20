import Langlands.Global.RankinSelberg.ComplexGodementTrailingPolynomial

/-! # Equivariance of the cofactor completion of a rectangular complex matrix -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "I" => Fin (n + 1)
local notation "Rect" => Matrix (Fin n) I ℂ
local notation "Square" => Matrix I I ℂ
local notation "K" => unitaryCompact ℂ (n + 1)

@[simp] theorem specialCompletion_succ (X : Rect) (i : Fin n) (j : I) :
    specialCompletion X i.succ j = X i j := rfl

@[simp] theorem trailingRows_specialCompletion (X : Rect) :
    trailingRows (specialCompletion X) = X := rfl

private def zeroTop (X : Rect) : Square := fun i j => Fin.cases 0 (fun r => X r j) i

private theorem zeroTop_mul (X : Rect) (A : Square) : zeroTop (X * A) = zeroTop X * A := by
  ext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · simp [zeroTop, Matrix.mul_apply]
  · rfl

private theorem specialCompletion_zero (X : Rect) (j : I) :
    specialCompletion X 0 j = star ((zeroTop X).adjugate j 0) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hs : (zeroTop X).submatrix (0 : I).succAbove j.succAbove = X.submatrix id j.succAbove := by
    ext r t
    simp [zeroTop, Matrix.submatrix_apply]
  rw [hs, star_mul', star_pow, star_neg, star_one]
  change _ * ((X.map (starRingEnd ℂ)).submatrix id j.succAbove).det = _
  rw [← show star (X.submatrix id j.succAbove).det =
      ((X.map (starRingEnd ℂ)).submatrix id j.succAbove).det from
    (starRingEnd ℂ).map_det _]
  simp only [Fin.val_zero, zero_add]

private theorem adjugate_eq_det_smul_conjTranspose (k : K) :
    k.val.val.adjugate = k.val.val.det • k.val.valᴴ := by
  have h : k.val.valᴴ * k.val.val = 1 := Unitary.star_mul_self_of_mem k.2
  calc
    _ = (k.val.valᴴ * k.val.val) * k.val.val.adjugate := by rw [h, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]

/-- Right multiplication by a unitary matrix commutes with completion up to the
reciprocal determinant in the new top row. -/
theorem specialCompletion_mul_unitary (X : Rect) (k : K) :
    specialCompletion (X * k.val.val) =
      Matrix.diagonal (Fin.cons (star k.val.val.det) 1) * (specialCompletion X * k.val.val) := by
  ext i j
  rw [Matrix.diagonal_mul]
  refine Fin.cases ?_ (fun r => ?_) i
  · rw [specialCompletion_zero, zeroTop_mul, Matrix.adjugate_mul_distrib,
      adjugate_eq_det_smul_conjTranspose, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Fin.cons_zero]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_mul', star_sum, star_star,
      specialCompletion_zero]
    congr 1
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  · simp [Matrix.mul_apply]

/-- The determinant of the completed matrix is invariant under right unitary multiplication. -/
theorem specialCompletion_det_mul_unitary (X : Rect) (k : K) :
    (specialCompletion (X * k.val.val)).det = (specialCompletion X).det := by
  rw [specialCompletion_mul_unitary, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_mul,
    Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Pi.one_apply, Finset.prod_const_one, mul_one]
  rw [mul_left_comm, Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary k.2), mul_one]

/-- Left multiplication of the rectangular rows scales the new top row by the
conjugate of the left determinant. -/
theorem specialCompletion_mul_left_zero (h : Matrix (Fin n) (Fin n) ℂ) (X : Rect) (j : I) :
    specialCompletion (h * X) 0 j = star h.det * specialCompletion X 0 j := by
  simp only [specialCompletion_zero, Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hs (Y : Rect) : (zeroTop Y).submatrix (0 : I).succAbove j.succAbove =
      Y.submatrix id j.succAbove := by
    ext r t
    simp [zeroTop, Matrix.submatrix_apply]
  have hmul : (h * X).submatrix id j.succAbove = h * X.submatrix id j.succAbove := by
    rw [Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
    rfl
  rw [hs, hs, hmul, Matrix.det_mul]
  simp only [star_mul']
  ring

/-- The cofactor completion is equivariant for right unitary multiplication, with the
specified scalar in the top row. -/
def ComplexGodementCompletionEquivarianceStatement : Prop :=
  ∀ (X : Rect) (k : K), specialCompletion (X * k.val.val) =
    Matrix.diagonal (Fin.cons (star k.val.val.det) 1) * (specialCompletion X * k.val.val)

theorem complexGodementCompletionEquivariance : ComplexGodementCompletionEquivarianceStatement (n := n) :=
  specialCompletion_mul_unitary

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
