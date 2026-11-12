import Langlands.GroupScheme.Quaternionic.Involution
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Scalar extension of matrices with involution -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.TensorMatrix

variable {K : Type u} {D : Type v} [CommRing K] [Ring D] [Algebra K D]
  (R : Type w) [CommRing R] [Algebra K R]
  (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Scalar extension commutes with rectangular matrices. -/
def rectangular : R ⊗[K] Matrix m n D ≃ₗ[K] Matrix m n (R ⊗[K] D) :=
  (TensorProduct.piRight K K R (fun _ : m => n → D)).trans
    (LinearEquiv.piCongrRight fun _ : m => TensorProduct.piRight K K R (fun _ : n => D))

@[simp] theorem rectangular_tmul (r : R) (M : Matrix m n D) :
    rectangular R m n (r ⊗ₜ[K] M) = fun i j => r ⊗ₜ[K] M i j := rfl

variable {m}

theorem rectangular_one : rectangular R n n (1 : R ⊗[K] Matrix n n D) = 1 := by
  rw [Algebra.TensorProduct.one_def, rectangular_tmul]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h, Algebra.TensorProduct.one_def]

theorem rectangular_mul (x y : R ⊗[K] Matrix n n D) :
    rectangular R n n (x * y) = rectangular R n n x * rectangular R n n y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [add_mul, _root_.map_add, hx, hx']
  | tmul r M =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [mul_add, _root_.map_add, hy, hy']
    | tmul s N =>
      ext i j
      simp [Algebra.TensorProduct.tmul_mul_tmul, Matrix.mul_apply, TensorProduct.tmul_sum]

/-- The same comparison as an algebra equivalence for square matrices. -/
def equiv : R ⊗[K] Matrix n n D ≃ₐ[K] Matrix n n (R ⊗[K] D) :=
  AlgEquiv.ofLinearEquiv (rectangular R n n) (rectangular_one R n) (rectangular_mul R n)

@[simp] theorem equiv_tmul (r : R) (M : Matrix n n D) :
    equiv R n (r ⊗ₜ[K] M) = fun i j => r ⊗ₜ[K] M i j := rfl

variable {R n}

/-- Entrywise comparison commutes with every coefficient-algebra morphism. -/
theorem naturality {S : Type w} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (x : R ⊗[K] Matrix n n D) :
    equiv S n (Algebra.TensorProduct.map f (AlgHom.id K _) x) =
      (equiv R n x).map (Algebra.TensorProduct.map f (AlgHom.id K D)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [_root_.map_add, hx, hy]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, _root_.map_add]
  | tmul r M => ext i j; simp

variable (σ : FirstKindInvolution K D) (R n)

/-- Scalar extension of the matrix adjoint is entrywise scalar extension of the involution. -/
theorem adjoint (x : R ⊗[K] Matrix n n D) :
    equiv R n ((σ.matrix n).baseChange R x) =
      (σ.baseChange R).matrix n (equiv R n x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [_root_.map_add, hx, hy]
  | tmul r M => ext i j; simp

/-- The actual alternating subspaces agree under the tensor-matrix comparison. -/
theorem mem_alternating_iff (x : R ⊗[K] Matrix n n D) :
    x ∈ ((σ.matrix n).baseChange R).alternatingSubspace ↔
      equiv R n x ∈ ((σ.baseChange R).matrix n).alternatingSubspace := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := ((σ.matrix n).baseChange R).mem_alternatingSubspace.mp h
    apply ((σ.baseChange R).matrix n).mem_alternatingSubspace.mpr
    exact ⟨equiv R n a, by rw [_root_.map_sub, adjoint]⟩
  · intro h
    obtain ⟨a, ha⟩ := ((σ.baseChange R).matrix n).mem_alternatingSubspace.mp h
    apply ((σ.matrix n).baseChange R).mem_alternatingSubspace.mpr
    refine ⟨(equiv R n).symm a, (equiv R n).injective ?_⟩
    rw [_root_.map_sub, adjoint, AlgEquiv.apply_symm_apply]
    exact ha

end Langlands.GroupScheme.Quaternionic.TensorMatrix
