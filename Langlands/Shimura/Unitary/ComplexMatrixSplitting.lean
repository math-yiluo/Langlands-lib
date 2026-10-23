import Langlands.Shimura.Unitary.DeligneSplitting
import Langlands.Shimura.Unitary.RealSplitting
import Mathlib.RingTheory.TensorProduct.Pi

noncomputable section
open Algebra Module
open scoped TensorProduct Classical

namespace Langlands.Shimura.ComplexMatrix

section General
variable (R S A : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Ring A] [Algebra R A] (n : ℕ)

/-- Distribute scalar extension over the finite array of matrix entries. -/
def tensorLinearEquiv :
    S ⊗[R] Matrix (Fin n) (Fin n) A ≃ₗ[S] Matrix (Fin n) (Fin n) (S ⊗[R] A) :=
  TensorProduct.piRight R S S (fun _ : Fin n => Fin n → A) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ : Fin n =>
      TensorProduct.piRight R S S (fun _ : Fin n => A))

@[simp] theorem tensorLinearEquiv_tmul (s : S) (M : Matrix (Fin n) (Fin n) A) :
    tensorLinearEquiv R S A n (s ⊗ₜ[R] M) = fun i j => s ⊗ₜ[R] M i j := rfl

/-- The entrywise tensor comparison preserves the actual matrix multiplication. -/
def tensorAlgEquiv :
    S ⊗[R] Matrix (Fin n) (Fin n) A ≃ₐ[S] Matrix (Fin n) (Fin n) (S ⊗[R] A) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (tensorLinearEquiv R S A n)
    (by
      intro s t M N
      ext i j
      change (s * t) ⊗ₜ[R] (∑ k, M i k * N k j) =
        ∑ k, (s ⊗ₜ[R] M i k) * (t ⊗ₜ[R] N k j)
      simp only [TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul])
    (by
      ext i j
      by_cases h : i = j <;>
        simp [Matrix.one_apply, h, Algebra.TensorProduct.one_def])

@[simp] theorem tensorAlgEquiv_tmul (s : S) (M : Matrix (Fin n) (Fin n) A) :
    tensorAlgEquiv R S A n (s ⊗ₜ[R] M) = fun i j => s ⊗ₜ[R] M i j := rfl

variable (B : Type*) [Ring B] [Algebra R B]

/-- A matrix over a product ring is the pair of its two component matrices. -/
def prodAlgEquiv : Matrix (Fin n) (Fin n) (A × B) ≃ₐ[R]
    Matrix (Fin n) (Fin n) A × Matrix (Fin n) (Fin n) B :=
  { ((AlgHom.fst R A B).mapMatrix).prod ((AlgHom.snd R A B).mapMatrix) with
    invFun := fun p i j => (p.1 i j, p.2 i j)
    left_inv := by intro M; rfl
    right_inv := by intro p; rfl }

@[simp] theorem prodAlgEquiv_apply (M : Matrix (Fin n) (Fin n) (A × B)) :
    prodAlgEquiv R A n B M = (fun i j => (M i j).1, fun i j => (M i j).2) := rfl

end General

/-- Scalar extension of a complex matrix algebra over the reals splits into two factors. -/
def complexEquiv (n : ℕ) :
    ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ]
      Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ :=
  (tensorAlgEquiv ℝ ℂ ℂ n).trans
    ((DeligneTorus.tensorSplitEquiv ℂ).mapMatrix.trans (prodAlgEquiv ℂ ℂ n ℂ))

@[simp] theorem tensorSplitEquiv_tmul (z w : ℂ) :
    DeligneTorus.tensorSplitEquiv ℂ (z ⊗ₜ[ℝ] w) = (z * w, z * star w) := by
  change DeligneTorus.splitEquiv ℂ (DeligneTorus.fromTensor ℂ (z ⊗ₜ[ℝ] w)) = _
  rw [DeligneTorus.fromTensor_tmul, DeligneTorus.splitEquiv_apply]
  apply Prod.ext <;> apply Complex.ext <;>
    simp [DeligneTorus.complexMap_re, DeligneTorus.complexMap_im,
      Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem complexEquiv_tmul (n : ℕ) (z : ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    complexEquiv n (z ⊗ₜ[ℝ] M) = (z • M, z • M.map star) := by
  apply Prod.ext
  · ext i j
    change (DeligneTorus.tensorSplitEquiv ℂ (z ⊗ₜ[ℝ] M i j)).1 = _
    simp [Matrix.smul_apply, smul_eq_mul]
  · ext i j
    change (DeligneTorus.tensorSplitEquiv ℂ (z ⊗ₜ[ℝ] M i j)).2 = _
    simp [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.HarrisSignatureCharts

universe u v w z
open NumberField
variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts σ n Φ)
  {ι : Type z} [Fintype ι] (b : Basis ι E A)

/-- The complex scalar extension of the real Harris algebra, in both matrix factors. -/
def iteratedComplexMatrixEquiv : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A) ≃ₐ[ℂ]
    ((E →+* ℝ) → Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ) (C.realMatrixEquiv b)).trans
    ((Algebra.TensorProduct.piRight ℝ ℂ ℂ
      (fun _ : E →+* ℝ => Matrix (Fin n) (Fin n) ℂ)).trans
      (AlgEquiv.piCongrRight (fun _ => ComplexMatrix.complexEquiv n)))

@[simp] theorem iteratedComplexMatrixEquiv_tmul (z : ℂ) (x : ℝ ⊗[ℚ] A)
    (τ : E →+* ℝ) :
    C.iteratedComplexMatrixEquiv b (z ⊗ₜ[ℝ] x) τ =
      (z • C.realMatrixEquiv b x τ, z • (C.realMatrixEquiv b x τ).map star) := by
  simp [iteratedComplexMatrixEquiv]

/-- Direct rational scalar extension has the same complex matrix decomposition. -/
def complexMatrixEquiv : ℂ ⊗[ℚ] A ≃ₐ[ℂ]
    ((E →+* ℝ) → Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :=
  (AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).trans
    (C.iteratedComplexMatrixEquiv b)

@[simp] theorem complexMatrixEquiv_tmul (z : ℂ) (a : A) (τ : E →+* ℝ) :
    C.complexMatrixEquiv b (z ⊗ₜ[ℚ] a) τ =
      (z • C.evaluation a τ, z • (C.evaluation a τ).map star) := by
  simp only [complexMatrixEquiv, AlgEquiv.trans_apply,
    AlgebraInvolution.baseChangeTowerEquiv_tmul, iteratedComplexMatrixEquiv_tmul,
    realMatrixEquiv_one_tmul]

end Langlands.Shimura.HarrisSignatureCharts
