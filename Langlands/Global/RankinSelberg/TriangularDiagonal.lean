import Langlands.Group.GL.TriangularParabolic
import Langlands.Group.GL.UpperUnipotent
import Langlands.GroupScheme.Rational.GeneralLinearCharacterMatrices
import Mathlib.Topology.Algebra.Group.Matrix

/-! # Diagonal units of upper triangular invertible matrices -/

noncomputable section
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.GaugeDescent

open Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear

variable {A : Type*} [CommRing A] {n : ℕ}

theorem triangular_mul_diag {b c : Matrix (Fin n) (Fin n) A}
    (hb : b.IsUpperTriangular) (hc : c.IsUpperTriangular) (i : Fin n) :
    (b * c) i i = b i i * c i i := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  intro j hji
  rcases lt_or_gt_of_ne hji with hji | hij
  · rw [hb hji, zero_mul]
  · rw [hc hij, mul_zero]

private theorem diag_mul_inv (b : upperTriangularSubgroup n A) (i : Fin n) :
    b.val i i * (b.val⁻¹) i i = 1 := by
  change b.val i i * (b⁻¹).val i i = 1
  rw [← triangular_mul_diag b.property (b⁻¹).property]
  have h : b.val * (b⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel b)
  simpa only [Units.val_mul, Units.val_one, Matrix.one_apply_eq] using
    congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) A =>
      (g : Matrix (Fin n) (Fin n) A) i i) h

/-- Diagonal entries of an invertible upper triangular matrix are units. -/
def triangularDiagonal (n : ℕ) (A : Type*) [CommRing A] :
    upperTriangularSubgroup n A →* (Fin n → Aˣ) where
  toFun b i :=
    { val := b.val i i
      inv := (b.val⁻¹) i i
      val_inv := diag_mul_inv b i
      inv_val := by rw [mul_comm]; exact diag_mul_inv b i }
  map_one' := by
    funext i
    apply Units.ext
    exact Matrix.one_apply_eq i
  map_mul' b c := by
    funext i
    apply Units.ext
    exact triangular_mul_diag b.property c.property i

@[simp] theorem triangularDiagonal_val (b : upperTriangularSubgroup n A) (i : Fin n) :
    (triangularDiagonal n A b i : A) = b.val i i := rfl

@[simp] theorem triangularDiagonal_inv_val (b : upperTriangularSubgroup n A) (i : Fin n) :
    ((triangularDiagonal n A b i)⁻¹ : Aˣ) = (b.val⁻¹) i i := rfl

theorem diagonalMatrixUnits_triangular (d : Fin n → Aˣ) :
    diagonalMatrixUnits A d ∈ upperTriangularSubgroup n A := by
  intro i j hji
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hji)

/-- The unitriangular factor obtained by removing the diagonal on the right. -/
def triangularUnipotent (b : upperTriangularSubgroup n A) : upperUnipotent n A :=
  ⟨b.val * (diagonalMatrixUnits A (triangularDiagonal n A b))⁻¹,
    (upperTriangularSubgroup n A).mul_mem b.property
      ((upperTriangularSubgroup n A).inv_mem (diagonalMatrixUnits_triangular _)),
    fun i => by
      change (b.val.val *
        ((diagonalMatrixUnits A (triangularDiagonal n A b))⁻¹).val) i i = 1
      rw [← map_inv, triangular_mul_diag b.property (diagonalMatrixUnits_triangular _)]
      rw [diagonalMatrixUnits_val, Matrix.diagonal_apply_eq]
      change b.val i i * ((triangularDiagonal n A b i)⁻¹ : Aˣ) = 1
      exact diag_mul_inv b i⟩

theorem triangularUnipotent_mul_diagonal (b : upperTriangularSubgroup n A) :
    (triangularUnipotent b).val * diagonalMatrixUnits A (triangularDiagonal n A b) =
      b.val := by
  exact inv_mul_cancel_right _ _

theorem triangularDiagonal_diagonal (d : Fin n → Aˣ) :
    triangularDiagonal n A ⟨diagonalMatrixUnits A d, diagonalMatrixUnits_triangular d⟩ =
      d := by
  funext i
  apply Units.ext
  exact Matrix.diagonal_apply_eq _ _

section Topology

variable [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_triangularDiagonal :
    Continuous (triangularDiagonal n A) := by
  apply continuous_pi
  intro i
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_apply i).comp (Matrix.GeneralLinearGroup.continuous_apply _
      continuous_subtype_val i)
  · exact (continuous_apply i).comp (Matrix.GeneralLinearGroup.continuous_apply _
      continuous_subtype_val.inv i)

variable [T2Space A]

omit [IsTopologicalRing A] in
theorem isClosed_upperTriangular :
    IsClosed (upperTriangularSubgroup n A : Set (Matrix.GeneralLinearGroup (Fin n) A)) :=
  isClosed_setOfPred_blockTriangular.preimage Units.continuous_val

end Topology

end Langlands.Global.RankinSelbergGlobal.GaugeDescent
