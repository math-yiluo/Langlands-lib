import Langlands.GroupScheme.Examples.SU3RootParameters
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace Langlands.GroupScheme.SU3Root

universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The split Hermitian form with middle coefficient -1. -/
def gram (A : Type u) [CommRing A] : Matrix (Fin 3) (Fin 3) A :=
  !![0, 0, 1; 0, -1, 0; 1, 0, 0]

/-- Conjugate transpose with respect to the specified ring involution. -/
def conjugateTranspose (c : RingInvolution A) (M : Matrix (Fin 3) (Fin 3) A) :=
  (M.map c.bar).transpose

/-- This is Mathlib's conjugate transpose when its star is the specified conjugation. -/
theorem conjugateTranspose_eq (c : RingInvolution A) (M : Matrix (Fin 3) (Fin 3) A) :
    letI : Star A := ⟨c.bar⟩
    conjugateTranspose c M = M.conjTranspose := rfl

/-- Preservation of the split Hermitian form. -/
def PreservesForm (c : RingInvolution A) (M : Matrix (Fin 3) (Fin 3) A) : Prop :=
  conjugateTranspose c M * gram A * M = gram A

/-- An upper triangular matrix with every diagonal entry equal to one. -/
def IsUpperUnipotent (M : Matrix (Fin 3) (Fin 3) A) : Prop :=
  (∀ i, M i i = 1) ∧ (∀ i j, j < i → M i j = 0)

namespace Parameters
variable {c : RingInvolution A} {d : RingInvolution B}

/-- The actual upper unipotent coordinate matrix. -/
def matrix (x : Parameters c) : Matrix (Fin 3) (Fin 3) A :=
  !![1, x.first, x.second; 0, 1, c.bar x.first; 0, 0, 1]

@[simp] theorem matrix_one : matrix (1 : Parameters c) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

theorem matrix_mul (x y : Parameters c) : matrix (x * y) = matrix x * matrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_three, map_add] <;> ring

/-- The coordinate matrix, made invertible using the coordinate inverse. -/
def embedding (c : RingInvolution A) : Parameters c →* Matrix.GeneralLinearGroup (Fin 3) A where
  toFun x :=
    { val := matrix x
      inv := matrix x⁻¹
      val_inv := by rw [← matrix_mul, mul_inv_cancel, matrix_one]
      inv_val := by rw [← matrix_mul, inv_mul_cancel, matrix_one] }
  map_one' := Units.ext matrix_one
  map_mul' x y := Units.ext (matrix_mul x y)

@[simp] theorem embedding_val (x : Parameters c) :
    ((embedding c x) : Matrix (Fin 3) (Fin 3) A) = matrix x := rfl

/-- Entry formula, with the same indices as the displayed three-by-three matrix. -/
theorem embedding_entries (x : Parameters c) :
    ((embedding c x) : Matrix (Fin 3) (Fin 3) A) =
      !![1, x.first, x.second; 0, 1, c.bar x.first; 0, 0, 1] := rfl

theorem embedding_injective (c : RingInvolution A) : Function.Injective (embedding c) := by
  intro x y h
  apply ext
  · exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) A => g 0 1) h
  · exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) A => g 0 2) h

@[simp] theorem matrix_det (x : Parameters c) : (matrix x).det = 1 := by
  simp [Matrix.det_fin_three, matrix]

@[simp] theorem embedding_det (x : Parameters c) :
    Matrix.GeneralLinearGroup.det (embedding c x) = 1 := by
  apply Units.ext
  exact matrix_det x

theorem matrix_upperUnipotent (x : Parameters c) : IsUpperUnipotent (matrix x) := by
  constructor
  · intro i; fin_cases i <;> rfl
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [matrix]

theorem matrix_preservesForm (x : Parameters c) : PreservesForm c (matrix x) := by
  unfold PreservesForm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugateTranspose, gram, matrix, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination x.equation

/-- An upper unipotent matrix is in the image exactly when it preserves the form. -/
theorem mem_range_embedding (g : Matrix.GeneralLinearGroup (Fin 3) A) :
    g ∈ (embedding c).range ↔
      IsUpperUnipotent (g : Matrix (Fin 3) (Fin 3) A) ∧
        PreservesForm c (g : Matrix (Fin 3) (Fin 3) A) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨matrix_upperUnipotent x, matrix_preservesForm x⟩
  · rintro ⟨⟨hdiag, hlow⟩, hform⟩
    let u := g 0 1
    let v := g 0 2
    let w := g 1 2
    have hshape : (g : Matrix (Fin 3) (Fin 3) A) = !![1, u, v; 0, 1, w; 0, 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> first | exact hdiag _ | exact hlow _ _ (by decide) | rfl
    unfold PreservesForm at hform
    rw [hshape] at hform
    have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 1 2) hform
    have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 2 2) hform
    simp [conjugateTranspose, gram, Matrix.mul_apply, Fin.sum_univ_three] at h12 h22
    have hw : w = c.bar u := by linear_combination -h12
    have hv : v + c.bar v = u * c.bar u := by
      rw [hw, RingInvolution.bar_bar] at h22
      linear_combination h22
    let x : Parameters c := ⟨(u, v), hv⟩
    refine ⟨x, ?_⟩
    apply Units.ext
    change matrix x = (g : Matrix (Fin 3) (Fin 3) A)
    rw [hshape]
    simp only [matrix, first, second, x, hw]

/-- The embedding commutes with every involution-compatible change of ring. -/
theorem embedding_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (x : Parameters c) :
    embedding d (map f hf x) = Matrix.GeneralLinearGroup.map f (embedding c x) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, hf]

end Parameters
end Langlands.GroupScheme.SU3Root
