import Langlands.GroupScheme.Examples.HermitianRootParameters
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Matrices for diagonal Hermitian root parameters -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v w

/-- Top, middle and bottom indices for a hyperbolic plane and a middle space. -/
abbrev Index (ι : Type v) := Unit ⊕ (ι ⊕ Unit)

variable {A : Type u} {B : Type w} {ι : Type v}
  [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]
  {c : RingInvolution A} {d : RingInvolution B}

/-- The hyperbolic plane together with the negative diagonal middle form. -/
def gram (H : DiagonalForm c ι) : Matrix (Index ι) (Index ι) A :=
  Matrix.fromBlocks 0
    (Matrix.of fun _ j => Sum.elim (fun _ => 0) (fun _ => 1) j)
    (Matrix.of fun i _ => Sum.elim (fun _ => 0) (fun _ => 1) i)
    (Matrix.fromBlocks (-Matrix.diagonal H.weight) 0 0 0)

/-- Conjugate transpose for the specified involution. -/
def conjugateTranspose (c : RingInvolution A)
    (M : Matrix (Index ι) (Index ι) A) : Matrix (Index ι) (Index ι) A :=
  (M.map c.bar).transpose

/-- Preservation of the hyperbolic-plus-middle Hermitian form. -/
def PreservesForm (H : DiagonalForm c ι) (M : Matrix (Index ι) (Index ι) A) : Prop :=
  conjugateTranspose c M * gram H * M = gram H

namespace Parameters

variable {H : DiagonalForm c ι} {K : DiagonalForm d ι}

/-- The upper block-unipotent matrix associated to the actual coordinates. -/
def matrix (x : Parameters H) : Matrix (Index ι) (Index ι) A :=
  Matrix.fromBlocks 1
    (Matrix.of fun _ j =>
      Sum.elim (fun i => H.weight i * x.vector i) (fun _ => x.scalar) j)
    0
    (Matrix.fromBlocks 1 (Matrix.of fun i _ => c.bar (x.vector i)) 0 1)

@[simp] theorem matrix_one : matrix (1 : Parameters H) = 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [matrix, Matrix.fromBlocks, Matrix.one_apply]

theorem matrix_mul (x y : Parameters H) : matrix (x * y) = matrix x * matrix y := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [matrix, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, DiagonalForm.pairing, mul_add, map_add] <;> ring

/-- An invertible matrix whose inverse is supplied by the coordinate inverse. -/
def embedding (H : DiagonalForm c ι) :
    Parameters H →* Matrix.GeneralLinearGroup (Index ι) A where
  toFun x :=
    { val := matrix x
      inv := matrix x⁻¹
      val_inv := by rw [← matrix_mul, mul_inv_cancel, matrix_one]
      inv_val := by rw [← matrix_mul, inv_mul_cancel, matrix_one] }
  map_one' := Units.ext matrix_one
  map_mul' x y := Units.ext (matrix_mul x y)

@[simp] theorem embedding_val (x : Parameters H) :
    ((embedding H x) : Matrix (Index ι) (Index ι) A) = matrix x := rfl

theorem matrix_injective : Function.Injective (matrix (H := H)) := by
  intro x y h
  apply ext
  · funext i
    have hi := congrArg
      (fun M : Matrix (Index ι) (Index ι) A => c.bar (M (Sum.inr (Sum.inl i))
        (Sum.inr (Sum.inr ())))) h
    simpa [matrix, Matrix.fromBlocks] using hi
  · exact congrArg
      (fun M : Matrix (Index ι) (Index ι) A => M (Sum.inl ())
        (Sum.inr (Sum.inr ()))) h

theorem embedding_injective : Function.Injective (embedding H) := by
  intro x y h
  apply matrix_injective
  exact congrArg (fun g : Matrix.GeneralLinearGroup (Index ι) A =>
    (g : Matrix (Index ι) (Index ι) A)) h

@[simp] theorem matrix_det (x : Parameters H) : (matrix x).det = 1 := by
  rw [matrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  simp

@[simp] theorem embedding_det (x : Parameters H) :
    Matrix.GeneralLinearGroup.det (embedding H x) = 1 := by
  apply Units.ext
  exact matrix_det x

theorem matrix_preservesForm (x : Parameters H) : PreservesForm H (matrix x) := by
  unfold PreservesForm
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [conjugateTranspose, gram, matrix, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply,
      Matrix.diagonal_apply, H.bar_weight] <;>
    try ring1
  have hp : (∑ k, x.vector k * H.weight k * c.bar (x.vector k)) =
      H.pairing x.vector x.vector := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hp]
  linear_combination x.equation

/-- Coordinate matrices commute with compatible coefficient changes. -/
theorem matrix_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i) (x : Parameters H) :
    matrix (map f hf hH x) = (matrix x).map f := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [matrix, Matrix.fromBlocks, Matrix.one_apply, hf, hH]

/-- The general-linear embedding commutes with compatible coefficient changes. -/
theorem embedding_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i) (x : Parameters H) :
    embedding K (map f hf hH x) = Matrix.GeneralLinearGroup.map f (embedding H x) := by
  apply Units.ext
  exact matrix_map f hf hH x

end Parameters
end Langlands.GroupScheme.HermitianRoot
