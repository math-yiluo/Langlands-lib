import Langlands.Algebra.MatrixSplitDefect
import Mathlib.RingTheory.MatrixAlgebra

/-! # Actual tensor-product matrix splitting charts -/

noncomputable section
universe u v w
open Matrix
open scoped TensorProduct Kronecker

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CentralSimple

namespace SemilinearGaloisAction

variable {k L : Type u} {C : Type v} {D : Type w} [Field k] [Field L] [Algebra k L]
  [Ring C] [Algebra L C] [Algebra k C] [IsScalarTower k L C]
  [Ring D] [Algebra L D] [Algebra k D] [IsScalarTower k L D]

/-- Transport of an actual semilinear action through an actual algebra equivalence. -/
def transport (ρ : SemilinearGaloisAction k L C) (e : C ≃ₐ[L] D) :
    SemilinearGaloisAction k L D where
  act σ := e.toRingHom.comp ((ρ.act σ).comp e.symm.toRingHom)
  act_algebraMap σ l := by
    change e (ρ.act σ (e.symm (algebraMap L D l))) = _
    rw [e.symm.commutes, ρ.act_algebraMap, e.commutes]
  act_one X := by
    change e (ρ.act 1 (e.symm X)) = X
    rw [ρ.act_one, e.apply_symm_apply]
  act_mul σ τ X := by
    change e (ρ.act (σ * τ) (e.symm X)) =
      e (ρ.act σ (e.symm (e (ρ.act τ (e.symm X)))))
    rw [e.symm_apply_apply, ρ.act_mul]

end SemilinearGaloisAction

variable {k L A B : Type u} [Field k] [Field L] [Algebra k L]
  [Ring A] [Algebra k A] [Ring B] [Algebra k B]

/-- The canonical actual semilinear coefficient action on a scalar-extended algebra. -/
def tensorCoefficientGaloisAction : SemilinearGaloisAction k L (L ⊗[k] A) where
  act σ := (tensorCoefficientMap σ).toRingHom
  act_algebraMap σ l := by
    change tensorCoefficientMap σ (l ⊗ₜ[k] (1 : A)) = σ l ⊗ₜ[k] (1 : A)
    exact tensorCoefficientMap_tmul σ l 1
  act_one := tensorCoefficientMap_one
  act_mul := tensorCoefficientMap_mul

/-- The actual chart action with an arbitrary finite matrix index type. -/
def splittingChartIndexAction {M : Type*} [Fintype M] [DecidableEq M]
    (e : L ⊗[k] A ≃ₐ[L] Matrix M M L) : SemilinearGaloisAction k L (Matrix M M L) :=
  tensorCoefficientGaloisAction.transport e

theorem splittingChartIndexAction_apply {M : Type*} [Fintype M] [DecidableEq M]
    (e : L ⊗[k] A ≃ₐ[L] Matrix M M L) (σ : L ≃ₐ[k] L) (X : L ⊗[k] A) :
    (splittingChartIndexAction e).act σ (e X) = e (tensorCoefficientMap σ X) := by
  change e (tensorCoefficientMap σ (e.symm (e X))) = _
  rw [e.symm_apply_apply]

/-- The arbitrary-index construction agrees with the earlier finite-size chart action. -/
theorem splittingChartIndexAction_fin_eq {n : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    splittingChartIndexAction e = splittingChartAction e := by
  rfl

/-- The actual interchange identifying two extended tensor factors with the
extension of their tensor product. -/
def scalarTensorInterchange :
    (L ⊗[k] A) ⊗[L] (L ⊗[k] B) ≃ₐ[L] L ⊗[k] (A ⊗[k] B) :=
  (Algebra.TensorProduct.tensorTensorTensorComm k k L L L A L B).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid L L)
      (AlgEquiv.refl : A ⊗[k] B ≃ₐ[k] A ⊗[k] B))

@[simp] theorem scalarTensorInterchange_tmul (l m : L) (a : A) (b : B) :
    scalarTensorInterchange ((l ⊗ₜ[k] a) ⊗ₜ[L] (m ⊗ₜ[k] b)) = (l * m) ⊗ₜ[k] (a ⊗ₜ[k] b) := by
  simp [scalarTensorInterchange, Algebra.TensorProduct.congr_apply]

@[simp] theorem scalarTensorInterchange_symm_tmul (l : L) (a : A) (b : B) :
    (scalarTensorInterchange (k := k) (L := L) (A := A) (B := B)).symm (l ⊗ₜ[k] (a ⊗ₜ[k] b)) =
      (l ⊗ₜ[k] a) ⊗ₜ[L] (1 ⊗ₜ[k] b) := by
  apply (scalarTensorInterchange (k := k) (L := L) (A := A) (B := B)).injective
  rw [AlgEquiv.apply_symm_apply, scalarTensorInterchange_tmul, mul_one]

/-- Coefficient automorphisms commute with the actual tensor interchange. -/
theorem scalarTensorInterchange_coefficientMap (σ : L ≃ₐ[k] L)
    (X : L ⊗[k] A) (Y : L ⊗[k] B) :
    tensorCoefficientMap σ (scalarTensorInterchange (X ⊗ₜ[L] Y)) =
      scalarTensorInterchange ((tensorCoefficientMap σ X) ⊗ₜ[L] (tensorCoefficientMap σ Y)) := by
  induction X with
  | tmul l a =>
    induction Y with
    | tmul m b => simp only [scalarTensorInterchange_tmul, tensorCoefficientMap_tmul, map_mul]
    | add Y Z hY hZ => simp only [TensorProduct.tmul_add, map_add, hY, hZ]
  | add X Z hX hZ => simp only [TensorProduct.add_tmul, map_add, hX, hZ]

variable {I : Type v} [Fintype I] [DecidableEq I]
  {J : Type w} [Fintype J] [DecidableEq J]

/-- The actual matrix chart of the tensor product of two supplied split algebras. -/
def tensorSplittingChart
    (eA : L ⊗[k] A ≃ₐ[L] Matrix I I L) (eB : L ⊗[k] B ≃ₐ[L] Matrix J J L) :
    L ⊗[k] (A ⊗[k] B) ≃ₐ[L] Matrix (I × J) (I × J) L :=
  (scalarTensorInterchange (k := k) (L := L) (A := A) (B := B)).symm.trans
    ((Algebra.TensorProduct.congr eA eB).trans (Matrix.kroneckerAlgEquiv I J L))

/-- The tensor-product chart is the actual Kronecker product on extended factors. -/
theorem tensorSplittingChart_interchange
    (eA : L ⊗[k] A ≃ₐ[L] Matrix I I L) (eB : L ⊗[k] B ≃ₐ[L] Matrix J J L)
    (X : L ⊗[k] A) (Y : L ⊗[k] B) :
    tensorSplittingChart eA eB (scalarTensorInterchange (X ⊗ₜ[L] Y)) = eA X ⊗ₖ eB Y := by
  simp [tensorSplittingChart, Algebra.TensorProduct.congr_apply]

@[simp] theorem tensorSplittingChart_tmul
    (eA : L ⊗[k] A ≃ₐ[L] Matrix I I L) (eB : L ⊗[k] B ≃ₐ[L] Matrix J J L)
    (l : L) (a : A) (b : B) :
    tensorSplittingChart eA eB (l ⊗ₜ[k] (a ⊗ₜ[k] b)) =
      eA (l ⊗ₜ[k] a) ⊗ₖ eB (1 ⊗ₜ[k] b) := by
  have h := tensorSplittingChart_interchange eA eB (l ⊗ₜ[k] a) (1 ⊗ₜ[k] b)
  simpa only [scalarTensorInterchange_tmul, mul_one] using h

/-- The actual tensor chart intertwines its coefficient action with the two
individual actual coefficient actions on every Kronecker product. -/
theorem tensorSplittingChart_action_kronecker
    (eA : L ⊗[k] A ≃ₐ[L] Matrix I I L) (eB : L ⊗[k] B ≃ₐ[L] Matrix J J L)
    (σ : L ≃ₐ[k] L) (X : Matrix I I L) (Y : Matrix J J L) :
    (splittingChartIndexAction (tensorSplittingChart eA eB)).act σ (X ⊗ₖ Y) =
      (splittingChartIndexAction eA).act σ X ⊗ₖ (splittingChartIndexAction eB).act σ Y := by
  obtain ⟨x, rfl⟩ := eA.surjective X
  obtain ⟨y, rfl⟩ := eB.surjective Y
  rw [← tensorSplittingChart_interchange, splittingChartIndexAction_apply,
    scalarTensorInterchange_coefficientMap, tensorSplittingChart_interchange,
    splittingChartIndexAction_apply, splittingChartIndexAction_apply]

end Langlands.CentralSimple

namespace Langlands.CentralSimple.SemilinearGaloisAction

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {I : Type v} [Fintype I] [DecidableEq I]
  {J : Type w} [Fintype J] [DecidableEq J]

attribute [local instance] coefficientGLAction

/-- Actual invertible Kronecker products preserve multiplication of both factors. -/
theorem kroneckerGL_mul (P R : GL I L) (Q S : GL J L) :
    (P * R).kronecker (Q * S) = P.kronecker Q * R.kronecker S := by
  apply Units.ext
  change ((P : Matrix I I L) * (R : Matrix I I L)) ⊗ₖ ((Q : Matrix J J L) * (S : Matrix J J L)) =
    ((P : Matrix I I L) ⊗ₖ (Q : Matrix J J L)) * ((R : Matrix I I L) ⊗ₖ (S : Matrix J J L))
  exact Matrix.mul_kronecker_mul (P : Matrix I I L) (R : Matrix I I L)
    (Q : Matrix J J L) (S : Matrix J J L)

/-- Coefficient automorphisms preserve actual invertible Kronecker products. -/
theorem coefficientGLAction_kronecker (σ : L ≃ₐ[k] L) (P : GL I L) (Q : GL J L) :
    σ • P.kronecker Q = (σ • P).kronecker (σ • Q) := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  exact map_mul σ (P i i') (Q j j')

/-- The actual Kronecker product of scalar matrices has the product unit scalar. -/
theorem scalar_kroneckerGL_scalar (a b : Lˣ) :
    (GeneralLinearGroup.scalar I a).kronecker (GeneralLinearGroup.scalar J b) =
      GeneralLinearGroup.scalar (I × J) (a * b) := by
  apply Units.ext
  change Matrix.scalar I (a : L) ⊗ₖ Matrix.scalar J (b : L) = Matrix.scalar (I × J) ((a : L) * b)
  exact Matrix.diagonal_kronecker_diagonal _ _

/-- The prescribed Kronecker inner lifts have the product of the two actual
scalar multiplication defects. -/
theorem kronecker_innerMatrix_mul
    (ρ : SemilinearGaloisAction k L (Matrix I I L))
    (θ : SemilinearGaloisAction k L (Matrix J J L)) (σ τ : L ≃ₐ[k] L) :
    (ρ.innerMatrix σ).kronecker (θ.innerMatrix σ) *
        (σ • (ρ.innerMatrix τ).kronecker (θ.innerMatrix τ)) =
      GeneralLinearGroup.scalar (I × J) (ρ.scalarDefect σ τ * θ.scalarDefect σ τ) *
        (ρ.innerMatrix (σ * τ)).kronecker (θ.innerMatrix (σ * τ)) := by
  rw [coefficientGLAction_kronecker, ← kroneckerGL_mul, ρ.innerMatrix_mul, θ.innerMatrix_mul,
    kroneckerGL_mul, scalar_kroneckerGL_scalar]

end Langlands.CentralSimple.SemilinearGaloisAction
