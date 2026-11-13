import Langlands.GroupScheme.Examples.SU3RootParameters
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Comparing a finite-source Hermitian presentation with the actual model -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

variable {A : Type u} [CommRing A] {ι : Type v} {κ : Type w}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
private theorem rectangular_conj_mul (P : Matrix κ ι A) (Q : Matrix ι κ A)
    (hQP : Q * P = 1) (g h : Matrix ι ι A) :
    (P * g * Q) * (P * h * Q) = P * (g * h) * Q := by
  calc
    _ = P * g * (Q * P) * h * Q := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hQP]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- Two-sided rectangular coordinate matrices conjugate actual general-linear
groups even when their finite index types differ. -/
def rectangularConjugationHom (P : Matrix κ ι A) (Q : Matrix ι κ A)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix.GeneralLinearGroup ι A →* Matrix.GeneralLinearGroup κ A where
  toFun g :=
    { val := P * (g : Matrix ι ι A) * Q
      inv := P * ((g⁻¹ : Matrix.GeneralLinearGroup ι A) : Matrix ι ι A) * Q
      val_inv := by
        rw [rectangular_conj_mul P Q hQP]
        simpa only [Units.val_inv_eq_inv_val, Units.mul_inv, Matrix.mul_one] using hPQ
      inv_val := by
        rw [rectangular_conj_mul P Q hQP]
        simpa only [Units.val_inv_eq_inv_val, Units.inv_mul, Matrix.mul_one] using hPQ }
  map_one' := Units.ext (by simpa only [Units.val_one, Matrix.mul_one] using hPQ)
  map_mul' g h := Units.ext (rectangular_conj_mul P Q hQP g h).symm

/-- The inverse matrix conjugation uses the reverse coordinates. -/
def rectangularConjugation (P : Matrix κ ι A) (Q : Matrix ι κ A)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix.GeneralLinearGroup ι A ≃* Matrix.GeneralLinearGroup κ A where
  toFun := rectangularConjugationHom P Q hPQ hQP
  invFun := rectangularConjugationHom Q P hQP hPQ
  left_inv g := by
    apply Units.ext
    change Q * (P * (g : Matrix ι ι A) * Q) * P = _
    calc
      _ = (Q * P) * (g : Matrix ι ι A) * (Q * P) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQP]; simp
  right_inv g := by
    apply Units.ext
    change P * (Q * (g : Matrix κ κ A) * P) * Q = _
    calc
      _ = (P * Q) * (g : Matrix κ κ A) * (P * Q) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPQ]; simp
  map_mul' := (rectangularConjugationHom P Q hPQ hQP).map_mul

@[simp] theorem rectangularConjugation_val
    (P : Matrix κ ι A) (Q : Matrix ι κ A)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (g : Matrix.GeneralLinearGroup ι A) :
    (rectangularConjugation P Q hPQ hQP g : Matrix κ κ A) =
      P * (g : Matrix ι ι A) * Q := rfl

/-- Rectangular conjugation preserves determinant, including over test rings. -/
@[simp] theorem rectangularConjugation_det
    (P : Matrix κ ι A) (Q : Matrix ι κ A)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (g : Matrix.GeneralLinearGroup ι A) :
    Matrix.GeneralLinearGroup.det (rectangularConjugation P Q hPQ hQP g) =
      Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  exact Matrix.det_conj_of_mul_eq_one hPQ hQP

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
private theorem rectangular_adjoint_mul (c : RingInvolution A)
    {η : Type*} [Fintype η] (M : Matrix ι η A) (N : Matrix η κ A) :
    ((M * N).map c.bar).transpose =
      (N.map c.bar).transpose * (M.map c.bar).transpose := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

omit [DecidableEq ι] in
/-- Multiplication by the reverse coordinates reverses the Gram congruence. -/
theorem rectangularGramCongruence_inv (c : RingInvolution A)
    (J : Matrix ι ι A) (B : Matrix κ κ A)
    (P : Matrix κ ι A) (Q : Matrix ι κ A)
    (hPQ : P * Q = 1)
    (hP : (P.map c.bar).transpose * B * P = J) :
    (Q.map c.bar).transpose * J * Q = B := by
  rw [← hP]
  calc
    _ = ((P * Q).map c.bar).transpose * B * (P * Q) := by
      rw [rectangular_adjoint_mul]
      simp only [Matrix.mul_assoc]
    _ = B := by rw [hPQ]; simp

omit [DecidableEq ι] in
private theorem rectangular_preserves (c : RingInvolution A)
    (J : Matrix ι ι A) (B : Matrix κ κ A)
    (P : Matrix κ ι A) (Q : Matrix ι κ A)
    (hPQ : P * Q = 1)
    (hP : (P.map c.bar).transpose * B * P = J)
    (g : Matrix ι ι A)
    (hg : (g.map c.bar).transpose * J * g = J) :
    ((P * g * Q).map c.bar).transpose * B * (P * g * Q) = B := by
  rw [rectangular_adjoint_mul, rectangular_adjoint_mul]
  calc
    _ = (Q.map c.bar).transpose *
        ((g.map c.bar).transpose *
          ((P.map c.bar).transpose * B * P) * g) * Q := by
      simp only [Matrix.mul_assoc]
    _ = B := by rw [hP, hg]; exact rectangularGramCongruence_inv c J B P Q hPQ hP

/-- Full form preservation is equivalent under the actual coordinate change. -/
theorem rectangularConjugation_preserves_iff (c : RingInvolution A)
    (J : Matrix ι ι A) (B : Matrix κ κ A)
    (P : Matrix κ ι A) (Q : Matrix ι κ A)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hP : (P.map c.bar).transpose * B * P = J)
    (g : Matrix.GeneralLinearGroup ι A) :
    (((rectangularConjugation P Q hPQ hQP g : Matrix κ κ A).map c.bar).transpose *
      B * (rectangularConjugation P Q hPQ hQP g : Matrix κ κ A) = B) ↔
      ((g : Matrix ι ι A).map c.bar).transpose * J *
        (g : Matrix ι ι A) = J := by
  constructor
  · intro hg
    have h := rectangular_preserves c B J Q P hQP
      (rectangularGramCongruence_inv c J B P Q hPQ hP) _ hg
    have he : Q * (P * (g : Matrix ι ι A) * Q) * P = (g : Matrix ι ι A) := by
      calc
        _ = (Q * P) * (g : Matrix ι ι A) * (Q * P) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hQP]; simp
    simpa only [rectangularConjugation_val, he] using h
  · exact rectangular_preserves c J B P Q hPQ hP _

end Langlands.GroupScheme.HermitianRoot
