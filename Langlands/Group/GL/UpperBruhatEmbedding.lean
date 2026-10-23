import Langlands.Group.GL.TriangularParabolic
import Langlands.Group.GL.Maps
import Mathlib.Logic.Equiv.Fin.Basic

namespace Langlands.GeneralLinear.Bruhat

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Add an isolated unit coordinate to a matrix. -/
def optionMatrix (M : Matrix (Fin n) (Fin n) R) :
    Matrix (Option (Fin n)) (Option (Fin n)) R
  | none, none => 1
  | some i, some j => M i j
  | _, _ => 0

@[simp] theorem optionMatrix_none_none (M : Matrix (Fin n) (Fin n) R) :
    optionMatrix M none none = 1 := rfl
@[simp] theorem optionMatrix_none_some (M : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    optionMatrix M none (some j) = 0 := rfl
@[simp] theorem optionMatrix_some_none (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    optionMatrix M (some i) none = 0 := rfl
@[simp] theorem optionMatrix_some_some (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    optionMatrix M (some i) (some j) = M i j := rfl

@[simp] theorem optionMatrix_one : optionMatrix (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [optionMatrix, Matrix.one_apply]

@[simp] theorem optionMatrix_mul (M N : Matrix (Fin n) (Fin n) R) :
    optionMatrix (M * N) = optionMatrix M * optionMatrix N := by
  ext i j
  cases i <;> cases j <;>
    simp [optionMatrix, Matrix.mul_apply, Fintype.sum_option]

/-- Add an isolated unit coordinate to an invertible matrix. -/
def optionGL (g : Langlands.GeneralLinear n R) :
    Matrix.GeneralLinearGroup (Option (Fin n)) R where
  val := optionMatrix g.val
  inv := optionMatrix g.inv
  val_inv := by rw [← optionMatrix_mul, g.val_inv, optionMatrix_one]
  inv_val := by rw [← optionMatrix_mul, g.inv_val, optionMatrix_one]

/-- Insert a fixed coordinate at `p`, retaining the increasing order elsewhere. -/
def insert (p : Fin (n + 1)) :
    Langlands.GeneralLinear n R →* Langlands.GeneralLinear (n + 1) R where
  toFun g := GeneralLinear.reindex (finSuccEquiv' p).symm (optionGL g)
  map_one' := by apply Units.ext; simp [GeneralLinear.reindex, optionGL]
  map_mul' g h := by
    apply Units.ext
    change Matrix.reindex (finSuccEquiv' p).symm (finSuccEquiv' p).symm
      (optionMatrix (g.val * h.val)) = _
    rw [optionMatrix_mul]
    exact (Matrix.submatrix_mul_equiv (optionMatrix g.val) (optionMatrix h.val)
      (finSuccEquiv' p) (finSuccEquiv' p) (finSuccEquiv' p)).symm

@[simp] theorem insert_apply (p : Fin (n + 1)) (g : Langlands.GeneralLinear n R)
    (i j : Fin (n + 1)) :
    insert p g i j = optionMatrix g.val (finSuccEquiv' p i) (finSuccEquiv' p j) := rfl

@[simp] theorem insert_p_p (p : Fin (n + 1)) (g : Langlands.GeneralLinear n R) :
    insert p g p p = 1 := by simp
@[simp] theorem insert_p_succAbove (p : Fin (n + 1)) (g : Langlands.GeneralLinear n R)
    (j : Fin n) : insert p g p (p.succAbove j) = 0 := by simp
@[simp] theorem insert_succAbove_p (p : Fin (n + 1)) (g : Langlands.GeneralLinear n R)
    (i : Fin n) : insert p g (p.succAbove i) p = 0 := by simp
@[simp] theorem insert_succAbove_succAbove (p : Fin (n + 1))
    (g : Langlands.GeneralLinear n R) (i j : Fin n) :
    insert p g (p.succAbove i) (p.succAbove j) = g i j := by simp

/-- Inserting an isolated coordinate preserves upper triangularity. -/
theorem insert_upper (p : Fin (n + 1)) (g : Langlands.GeneralLinear n R)
    (hg : ∀ i j : Fin n, j < i → g i j = 0) :
    ∀ i j : Fin (n + 1), j < i → insert p g i j = 0 := by
  intro i j hij
  induction i using Fin.succAboveCases p with
  | x =>
    induction j using Fin.succAboveCases p with
    | x => exact False.elim (lt_irrefl _ hij)
    | p j => simp
  | p i =>
    induction j using Fin.succAboveCases p with
    | x => simp
    | p j =>
      rw [insert_succAbove_succAbove]
      exact hg i j (Fin.succAbove_lt_succAbove_iff.mp hij)

/-- Extend a permutation, sending the omitted column to the last row. -/
def extendPerm (p : Fin (n + 1)) (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' p).trans ((Equiv.optionCongr w).trans finSuccEquivLast.symm)

@[simp] theorem extendPerm_p (p : Fin (n + 1)) (w : Equiv.Perm (Fin n)) :
    extendPerm p w p = Fin.last n := by simp [extendPerm]

@[simp] theorem extendPerm_succAbove (p : Fin (n + 1)) (w : Equiv.Perm (Fin n))
    (j : Fin n) : extendPerm p w (p.succAbove j) = (w j).castSucc := by
  simp [extendPerm, finSuccEquivLast_symm_some]

end Langlands.GeneralLinear.Bruhat
