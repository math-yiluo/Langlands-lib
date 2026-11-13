import Langlands.GroupScheme.Torus.FiniteMatrixAlgebraWeightBasis
import Langlands.GroupScheme.FiniteAlgebraMatrixPoints
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! # Laurent matrices of finite matrix algebra tori -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open FiniteAlgebraUnits FiniteAlgebraTorusWeights SplitTorusRepresentationWeights

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {M : Type u} [AddCommMonoid M]

/-- Swap tensor factors and identify scalar-extended monoid algebras. -/
def laurentCoefficients : AddMonoidAlgebra K M ⊗[K] L ≃ₐ[K] AddMonoidAlgebra L M :=
  (Algebra.TensorProduct.comm K _ L).trans
    ((AddMonoidAlgebra.scalarTensorEquiv K L).restrictScalars K)

@[simp] theorem laurentCoefficients_single_tmul (m : M) (a : L) :
    laurentCoefficients K L (AddMonoidAlgebra.single m (1 : K) ⊗ₜ[K] a) =
      AddMonoidAlgebra.single m a := by
  change AddMonoidAlgebra.scalarTensorEquiv K L
    (a ⊗ₜ[K] AddMonoidAlgebra.single m (1 : K)) = _
  rw [← AddMonoidAlgebra.scalarTensorEquiv_symm_single]
  exact AlgEquiv.apply_symm_apply _ _

/-- Move the tensor factor through matrices and recover Laurent coefficients. -/
def laurentMatrixEquiv {N : ℕ} :
    AddMonoidAlgebra K M ⊗[K] Matrix (Fin N) (Fin N) L ≃ₐ[K]
      Matrix (Fin N) (Fin N) (AddMonoidAlgebra L M) :=
  (MatrixPoints.coefficientEquiv K L (AddMonoidAlgebra K M)).trans
    (laurentCoefficients K L).mapMatrix

@[simp] theorem laurentMatrixEquiv_single_tmul {N : ℕ}
    (m : M) (A : Matrix (Fin N) (Fin N) L) (r c : Fin N) :
    laurentMatrixEquiv K L (AddMonoidAlgebra.single m (1 : K) ⊗ₜ[K] A) r c =
      AddMonoidAlgebra.single m (A r c) := by
  simp only [laurentMatrixEquiv, AlgEquiv.trans_apply, AlgEquiv.mapMatrix_apply,
    Matrix.map_apply]
  rw [MatrixPoints.coefficientEquiv_tmul, laurentCoefficients_single_tmul]

variable {K L} {N d : ℕ}
  {b : Module.Basis (Fin d) K (Matrix (Fin N) (Fin N) L)}
  {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ groupScheme b)

/-- The inverse universal unit viewed as a matrix over the L-valued Laurent ring. -/
def inverseUniversalMatrix :
    Matrix.GeneralLinearGroup (Fin N) (AddMonoidAlgebra L (I → ℤ)) :=
  Units.mapEquiv (laurentMatrixEquiv K L (M := I → ℤ) (N := N)).toMulEquiv (universalUnit i)⁻¹

/-- Laurent expansion of the actual inverse universal matrix. -/
theorem inverseUniversalMatrix_eq_sum :
    (inverseUniversalMatrix i : Matrix (Fin N) (Fin N) (AddMonoidAlgebra L (I → ℤ))) =
      ∑ m ∈ weightSupport (rightRegularRepresentation b) I i,
        fun r c => AddMonoidAlgebra.single m (weightElement i m r c) := by
  change laurentMatrixEquiv K L (M := I → ℤ) (N := N)
    (↑((universalUnit i)⁻¹) :
      AddMonoidAlgebra K (I → ℤ) ⊗[K] Matrix (Fin N) (Fin N) L) = _
  rw [universalUnit_inv_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  funext r c
  exact laurentMatrixEquiv_single_tmul K L m _ r c

omit [Fintype I] [DecidableEq I] in
/-- A monomial matrix acts on constant vectors by the underlying field matrix. -/
theorem singleMatrix_mulVec (m : I → ℤ) (A : Matrix (Fin N) (Fin N) L)
    (v : Fin N → L) :
    (fun r c => AddMonoidAlgebra.single m (A r c)) *ᵥ
        (fun c => AddMonoidAlgebra.single 0 (v c)) =
      fun r => AddMonoidAlgebra.single m ((A *ᵥ v) r) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, AddMonoidAlgebra.single_mul_single, add_zero]
  exact (map_sum (AddMonoidAlgebra.singleAddHom m) _ _).symm

/-- The projector eigenvector rule gives the Laurent eigenvector equation. -/
theorem inverseUniversalMatrix_mulVec {m : I → ℤ}
    (hm : m ∈ weightSupport (rightRegularRepresentation b) I i)
    (v : Fin N → L)
    (hv : ∀ p, weightElement i p *ᵥ v = if p = m then v else 0) :
    (inverseUniversalMatrix i : Matrix (Fin N) (Fin N) (AddMonoidAlgebra L (I → ℤ))) *ᵥ
        (fun c => AddMonoidAlgebra.single 0 (v c)) =
      fun r => AddMonoidAlgebra.single m (v r) := by
  rw [inverseUniversalMatrix_eq_sum, Matrix.sum_mulVec]
  simp_rw [singleMatrix_mulVec, hv]
  funext r
  simp only [Finset.sum_apply]
  simp [ite_apply, apply_ite, hm]

/-- Selected projector-column basis labels all occur in the regular weight support. -/
theorem mem_weightSupport_of_basis_column
    (v : Module.Basis (Fin N) L (Fin N → L))
    (q : Fin N → (I → ℤ) × Fin N)
    (hv : ∀ j, v j = weightColumn i (q j)) (j : Fin N) :
    (q j).1 ∈ weightSupport (rightRegularRepresentation b) I i := by
  classical
  by_contra hn
  apply v.ne_zero j
  rw [hv, weightColumn, MatrixIdempotentBasis.columnFamily, weightElement_eq_zero i hn]
  rfl

end Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights
