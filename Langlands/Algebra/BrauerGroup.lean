import Langlands.Algebra.CentralSimpleTensor
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.Unique

/-! # Operations on the actual matrix-stable Brauer quotient -/

noncomputable section

namespace Langlands.Brauer

universe u v w

open scoped TensorProduct

variable {K : Type u} [Field K]

/-- The one-by-one matrix chart with the standard `Fin` matrix instances. -/
def matrixOneEquiv (A : Type v) [Ring A] [Algebra K A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[K] A where
  toFun M := M 0 0
  invFun a := fun _ _ => a
  left_inv M := by ext i j; fin_cases i; fin_cases j; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := by simp [Matrix.mul_apply]
  commutes' r := by
    simp only [Matrix.algebraMap_matrix_apply, ite_true]

/-- An actual algebra equivalence gives matrix-stable equivalence. -/
theorem equivalent_of_algEquiv {A B : CSA.{u, v} K} (e : A ≃ₐ[K] B) :
    IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

/-- Matrices commute with tensoring the coefficient algebra on the right. -/
def matrixTensorEquiv (A : CSA.{u, v} K) (B : CSA.{u, w} K) (n : ℕ) :
    Matrix (Fin n) (Fin n) A ⊗[K] B ≃ₐ[K]
      Matrix (Fin n) (Fin n) (A ⊗[K] B) :=
  (Algebra.TensorProduct.congr (matrixEquivTensor (Fin n) K A)
    (AlgEquiv.refl : B ≃ₐ[K] B)).trans <|
  (Algebra.TensorProduct.assoc K K K A (Matrix (Fin n) (Fin n) K) B).trans <|
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[K] A)
    (Algebra.TensorProduct.comm K (Matrix (Fin n) (Fin n) K) B)).trans <|
  (Algebra.TensorProduct.assoc K K K A B (Matrix (Fin n) (Fin n) K)).symm.trans <|
  (matrixEquivTensor (Fin n) K (A ⊗[K] B)).symm

theorem equivalent_tensor_left {A A' : CSA.{u, v} K}
    (h : IsBrauerEquivalent A A') (B : CSA.{u, w} K) :
    IsBrauerEquivalent (tensor A B) (tensor A' B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ⟨?_⟩⟩
  exact (matrixTensorEquiv A B n).symm.trans <|
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : B ≃ₐ[K] B)).trans <|
    matrixTensorEquiv A' B m

theorem equivalent_tensor_right (A : CSA.{u, v} K)
    {B B' : CSA.{u, w} K} (h : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (tensor A B) (tensor A B') :=
  (equivalent_of_algEquiv (Algebra.TensorProduct.comm K A B)).trans <|
    (equivalent_tensor_left h A).trans <|
    equivalent_of_algEquiv (Algebra.TensorProduct.comm K B' A)

theorem equivalent_opposite {A B : CSA.{u, v} K}
    (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (opposite A) (opposite B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨AlgEquiv.mopMatrix.trans <|
    e.op.trans AlgEquiv.mopMatrix.symm⟩⟩

/-- An actual CSA's class in Mathlib's matrix-stable quotient. -/
def classOf (A : CSA.{u, u} K) : BrauerGroup.{u, u} K :=
  Quotient.mk (Brauer.CSA_Setoid K) A

theorem classOf_eq_iff (A B : CSA.{u, u} K) :
    classOf A = classOf B ↔ IsBrauerEquivalent A B :=
  Quotient.eq

theorem classOf_eq_of_algEquiv {A B : CSA.{u, u} K} (e : A ≃ₐ[K] B) :
    classOf A = classOf B :=
  Quotient.sound (equivalent_of_algEquiv e)

instance instZeroBrauerGroup : Zero (BrauerGroup.{u, u} K) :=
  ⟨classOf (groundField K)⟩

instance instAddBrauerGroup : Add (BrauerGroup.{u, u} K) :=
  ⟨Quotient.lift₂ (fun A B => classOf (tensor A B)) fun _ _ _ _ hA hB =>
    Quotient.sound <| (equivalent_tensor_left hA _).trans (equivalent_tensor_right _ hB)⟩

instance instNegBrauerGroup : Neg (BrauerGroup.{u, u} K) :=
  ⟨Quotient.lift (fun A => classOf (opposite A)) fun _ _ h =>
    Quotient.sound (equivalent_opposite h)⟩

@[simp] theorem classOf_groundField : classOf (groundField K) = 0 := rfl

@[simp] theorem classOf_tensor (A B : CSA.{u, u} K) :
    classOf (tensor A B) = classOf A + classOf B := rfl

@[simp] theorem classOf_opposite (A : CSA.{u, u} K) :
    classOf (opposite A) = -classOf A := rfl

@[simp] theorem classOf_matrix (A : CSA.{u, u} K) (n : ℕ) [NeZero n] :
    classOf (matrix A n) = classOf A :=
  Quotient.sound ⟨1, n, one_ne_zero, NeZero.ne n,
    ⟨matrixOneEquiv (Matrix (Fin n) (Fin n) A)⟩⟩

theorem tensor_opposite_equivalent (A : CSA.{u, u} K) :
    IsBrauerEquivalent (tensor A (opposite A)) (groundField K) := by
  let n := Module.finrank K A
  have hn : n ≠ 0 := Nat.ne_of_gt Module.finrank_pos
  refine ⟨1, n, one_ne_zero, hn, ⟨?_⟩⟩
  exact (matrixOneEquiv (A ⊗[K] Aᵐᵒᵖ)).trans <|
    (CentralSimple.envelopingEquiv K A).trans <|
    LinearMap.toMatrixAlgEquiv (Module.finBasis K A)

instance instAddCommGroupBrauerGroup : AddCommGroup (BrauerGroup.{u, u} K) where
  add_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
    induction c using Quotient.inductionOn with | _ C =>
    exact classOf_eq_of_algEquiv (Algebra.TensorProduct.assoc K K K A B C)
  zero_add := by
    intro a
    induction a using Quotient.inductionOn with | _ A =>
    exact classOf_eq_of_algEquiv (Algebra.TensorProduct.lid K A)
  add_zero := by
    intro a
    induction a using Quotient.inductionOn with | _ A =>
    exact classOf_eq_of_algEquiv (Algebra.TensorProduct.rid K K A)
  neg_add_cancel := by
    intro a
    induction a using Quotient.inductionOn with | _ A =>
    exact Quotient.sound <|
      (equivalent_of_algEquiv (Algebra.TensorProduct.comm K Aᵐᵒᵖ A)).trans <|
      tensor_opposite_equivalent A
  add_comm := by
    intro a b
    induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
    exact classOf_eq_of_algEquiv (Algebra.TensorProduct.comm K A B)
  nsmul := nsmulRec
  zsmul := zsmulRec

end Langlands.Brauer
