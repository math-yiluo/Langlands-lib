import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Trace

noncomputable section

universe u

namespace Langlands.LinearAlgebra

open Matrix Topology

/-- The index of the trivial, standard, and inverse-adjoint summands. -/
abbrev InverseAdjointIndex (I : Type u) := Unit ⊕ (I ⊕ I)

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- The augmented inverse-adjoint representation matrix. -/
def inverseAdjointMatrix (A : Matrix.GeneralLinearGroup I ℂ) :
    Matrix (InverseAdjointIndex I) (InverseAdjointIndex I) ℂ :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks (↑A) 0 0 (↑(A⁻¹) : Matrix I I ℂ)ᴴ)

@[simp] theorem inverseAdjointMatrix_scalar (A : Matrix.GeneralLinearGroup I ℂ) :
    inverseAdjointMatrix A (.inl ()) (.inl ()) = 1 := rfl

@[simp] theorem inverseAdjointMatrix_standard (A : Matrix.GeneralLinearGroup I ℂ) (i j : I) :
    inverseAdjointMatrix A (.inr (.inl i)) (.inr (.inl j)) = A i j := rfl

@[simp] theorem inverseAdjointMatrix_dual (A : Matrix.GeneralLinearGroup I ℂ) (i j : I) :
    inverseAdjointMatrix A (.inr (.inr i)) (.inr (.inr j)) = star (A⁻¹ j i) := rfl

@[simp] theorem inverseAdjointMatrix_one :
    inverseAdjointMatrix (1 : Matrix.GeneralLinearGroup I ℂ) = 1 := by
  simp [inverseAdjointMatrix, Matrix.fromBlocks_one]

@[simp] theorem inverseAdjointMatrix_mul (A B : Matrix.GeneralLinearGroup I ℂ) :
    inverseAdjointMatrix (A * B) = inverseAdjointMatrix A * inverseAdjointMatrix B := by
  simp [inverseAdjointMatrix, Matrix.fromBlocks_multiply, Matrix.conjTranspose_mul]

/-- The matrix-valued monoid homomorphism. -/
def inverseAdjointMatrixHom : Matrix.GeneralLinearGroup I ℂ →*
    Matrix (InverseAdjointIndex I) (InverseAdjointIndex I) ℂ where
  toFun := inverseAdjointMatrix
  map_one' := inverseAdjointMatrix_one
  map_mul' := inverseAdjointMatrix_mul

/-- The representation on the actual complex Euclidean Hilbert space. -/
def inverseAdjointRepresentation : Matrix.GeneralLinearGroup I ℂ →*
    (EuclideanSpace ℂ (InverseAdjointIndex I) →L[ℂ]
      EuclideanSpace ℂ (InverseAdjointIndex I)) :=
  Matrix.toEuclideanCLM.toMonoidHom.comp inverseAdjointMatrixHom

@[simp] theorem inverseAdjointRepresentation_apply (A : Matrix.GeneralLinearGroup I ℂ)
    (x : EuclideanSpace ℂ (InverseAdjointIndex I)) :
    WithLp.ofLp (inverseAdjointRepresentation A x) =
      inverseAdjointMatrix A *ᵥ WithLp.ofLp x := rfl

private def inverseAdjointBlockLinear :
    (Matrix I I ℂ × Matrix I I ℂ) →ₗ[ℝ]
      Matrix (InverseAdjointIndex I) (InverseAdjointIndex I) ℂ where
  toFun p := Matrix.fromBlocks 0 0 0 (Matrix.fromBlocks p.1 0 0 p.2ᴴ)
  map_add' p q := by
    simp [Matrix.fromBlocks_add, Matrix.conjTranspose_add]
  map_smul' r p := by
    simp [Matrix.fromBlocks_smul, Matrix.conjTranspose_smul]

omit [Fintype I] [DecidableEq I] in
private theorem inverseAdjointBlockLinear_injective :
    Function.Injective (inverseAdjointBlockLinear (I := I)) := by
  intro p q h
  apply Prod.ext
  · exact Matrix.ext fun i j => congrArg
      (fun M => M (.inr (.inl i)) (.inr (.inl j))) h
  · apply Matrix.ext
    intro i j
    have e := congrArg (fun M => M (.inr (.inr j)) (.inr (.inr i))) h
    exact star_injective e

/-- The inverse-adjoint matrices form a closed embedded copy of GL in the entire matrix space. -/
theorem isClosedEmbedding_inverseAdjointMatrix :
    IsClosedEmbedding (inverseAdjointMatrix (I := I)) := by
  let C : Matrix (InverseAdjointIndex I) (InverseAdjointIndex I) ℂ :=
    Matrix.fromBlocks 1 0 0 0
  have hpair : IsClosedEmbedding (fun A : Matrix.GeneralLinearGroup I ℂ =>
      ((↑A : Matrix I I ℂ), (↑(A⁻¹) : Matrix I I ℂ))) :=
    ((Homeomorph.refl (Matrix I I ℂ)).prodCongr
      MulOpposite.opHomeomorph.symm).isClosedEmbedding.comp
      Units.isClosedEmbedding_embedProduct
  have hlin := LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (inverseAdjointBlockLinear_injective (I := I)))
  have h := (Homeomorph.addLeft C).isClosedEmbedding.comp (hlin.comp hpair)
  convert h using 1
  funext A
  simp [C, inverseAdjointMatrix, inverseAdjointBlockLinear, Matrix.fromBlocks_add]

theorem continuous_inverseAdjointMatrix : Continuous (inverseAdjointMatrix (I := I)) :=
  isClosedEmbedding_inverseAdjointMatrix.continuous

theorem inverseAdjointMatrix_injective : Function.Injective (inverseAdjointMatrix (I := I)) :=
  isClosedEmbedding_inverseAdjointMatrix.injective

theorem isClosed_range_inverseAdjointMatrix :
    IsClosed (Set.range (inverseAdjointMatrix (I := I))) :=
  isClosedEmbedding_inverseAdjointMatrix.isClosed_range

/-- The same closed embedding, now into the full complex continuous endomorphism space. -/
theorem isClosedEmbedding_inverseAdjointRepresentation :
    IsClosedEmbedding (inverseAdjointRepresentation (I := I)) :=
  (Matrix.toEuclideanCLM (n := InverseAdjointIndex I) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.comp
    isClosedEmbedding_inverseAdjointMatrix

theorem continuous_inverseAdjointRepresentation :
    Continuous (inverseAdjointRepresentation (I := I)) :=
  isClosedEmbedding_inverseAdjointRepresentation.continuous

theorem inverseAdjointRepresentation_injective :
    Function.Injective (inverseAdjointRepresentation (I := I)) :=
  isClosedEmbedding_inverseAdjointRepresentation.injective

theorem isClosed_range_inverseAdjointRepresentation :
    IsClosed (Set.range (inverseAdjointRepresentation (I := I))) :=
  isClosedEmbedding_inverseAdjointRepresentation.isClosed_range

/-- On unitary input the inverse-adjoint block is the original matrix. -/
theorem inverseAdjointMatrix_of_unitary (A : Matrix.GeneralLinearGroup I ℂ)
    (hA : (↑A : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ) :
    inverseAdjointMatrix A = Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks (↑A) 0 0 (↑A)) := by
  have h : (↑(A⁻¹) : Matrix I I ℂ) = (↑A : Matrix I I ℂ)ᴴ :=
    left_inv_eq_right_inv A.inv_mul (Unitary.mul_star_self_of_mem hA)
  simp [inverseAdjointMatrix, h]

/-- A unitary input has a unitary augmented matrix. -/
theorem inverseAdjointMatrix_mem_unitary (A : Matrix.GeneralLinearGroup I ℂ)
    (hA : (↑A : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ) :
    inverseAdjointMatrix A ∈ Matrix.unitaryGroup (InverseAdjointIndex I) ℂ := by
  rw [inverseAdjointMatrix_of_unitary A hA, Matrix.mem_unitaryGroup_iff]
  have h : (↑A : Matrix I I ℂ) * (↑A : Matrix I I ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem hA
  simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, h, Matrix.fromBlocks_one]

/-- Unitary input acts by a unitary operator on the actual complex Hilbert space. -/
theorem inverseAdjointRepresentation_mem_unitary (A : Matrix.GeneralLinearGroup I ℂ)
    (hA : (↑A : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ) :
    inverseAdjointRepresentation A ∈ unitary
      (EuclideanSpace ℂ (InverseAdjointIndex I) →L[ℂ] EuclideanSpace ℂ (InverseAdjointIndex I)) :=
  Unitary.map_mem (Matrix.toEuclideanCLM (n := InverseAdjointIndex I) (𝕜 := ℂ))
    (inverseAdjointMatrix_mem_unitary A hA)

theorem inverseAdjointRepresentation_inner (A : Matrix.GeneralLinearGroup I ℂ)
    (hA : (↑A : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ)
    (x y : EuclideanSpace ℂ (InverseAdjointIndex I)) :
    inner ℂ (inverseAdjointRepresentation A x) (inverseAdjointRepresentation A y) = inner ℂ x y :=
  (inverseAdjointRepresentation A).inner_map_map_of_mem_unitary
    (inverseAdjointRepresentation_mem_unitary A hA) x y

/-- The squared Hilbert–Schmidt norm, expressed in the standard orthonormal coordinates. -/
def inverseAdjointHilbertSchmidtSq (A : Matrix.GeneralLinearGroup I ℂ) : ℝ :=
  ∑ i, ∑ j, ‖inverseAdjointMatrix A i j‖ ^ 2

/-- The scalar summand contributes one; conjugate transpose preserves the sum of squared entries. -/
theorem inverseAdjointHilbertSchmidtSq_eq (A : Matrix.GeneralLinearGroup I ℂ) :
    inverseAdjointHilbertSchmidtSq A =
      1 + (∑ i, ∑ j, ‖A i j‖ ^ 2) + ∑ i, ∑ j, ‖A⁻¹ i j‖ ^ 2 := by
  simp only [inverseAdjointHilbertSchmidtSq, inverseAdjointMatrix, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, add_zero, zero_add, Finset.sum_add_distrib]
  simp only [Matrix.conjTranspose_apply, norm_star, Matrix.one_apply_eq,
    norm_one, one_pow, Fintype.sum_unique, add_assoc]
  have hs : (∑ i, ∑ j, ‖A⁻¹ j i‖ ^ 2) = ∑ i, ∑ j, ‖A⁻¹ i j‖ ^ 2 :=
    Finset.sum_comm
  rw [hs]

theorem one_le_inverseAdjointHilbertSchmidtSq (A : Matrix.GeneralLinearGroup I ℂ) :
    1 ≤ inverseAdjointHilbertSchmidtSq A := by
  rw [inverseAdjointHilbertSchmidtSq_eq]
  have h₁ : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h₂ : 0 ≤ ∑ i, ∑ j, ‖A⁻¹ i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem inverseAdjointHilbertSchmidtSq_pos (A : Matrix.GeneralLinearGroup I ℂ) :
    0 < inverseAdjointHilbertSchmidtSq A :=
  lt_of_lt_of_le zero_lt_one (one_le_inverseAdjointHilbertSchmidtSq A)

/-- The entry formula is exactly the trace of the adjoint times the matrix. -/
theorem inverseAdjointHilbertSchmidtSq_eq_matrix_trace (A : Matrix.GeneralLinearGroup I ℂ) :
    inverseAdjointHilbertSchmidtSq A =
      ((inverseAdjointMatrix A)ᴴ * inverseAdjointMatrix A).trace.re := by
  have h : ((inverseAdjointMatrix A)ᴴ * inverseAdjointMatrix A).trace =
      ((∑ i, ∑ j, ‖inverseAdjointMatrix A j i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      ← starRingEnd_apply, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re, inverseAdjointHilbertSchmidtSq, Finset.sum_comm]

/-- The same square is the trace computed using the Hilbert-space adjoint of the operator. -/
theorem inverseAdjointHilbertSchmidtSq_eq_trace (A : Matrix.GeneralLinearGroup I ℂ) :
    inverseAdjointHilbertSchmidtSq A =
      (LinearMap.trace ℂ (EuclideanSpace ℂ (InverseAdjointIndex I))
        (star (inverseAdjointRepresentation A) * inverseAdjointRepresentation A).toLinearMap).re := by
  have h : star (inverseAdjointRepresentation A) * inverseAdjointRepresentation A =
      Matrix.toEuclideanCLM (n := InverseAdjointIndex I) (𝕜 := ℂ) ((inverseAdjointMatrix A)ᴴ * inverseAdjointMatrix A) := by
    change star (Matrix.toEuclideanCLM (n := InverseAdjointIndex I) (𝕜 := ℂ) (inverseAdjointMatrix A)) *
      Matrix.toEuclideanCLM (n := InverseAdjointIndex I) (𝕜 := ℂ) (inverseAdjointMatrix A) = _
    rw [map_mul, ← Matrix.star_eq_conjTranspose, map_star]
  rw [h, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (InverseAdjointIndex I) ℂ).toBasis,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  exact inverseAdjointHilbertSchmidtSq_eq_matrix_trace A

/-- The Hilbert–Schmidt norm of the augmented representation, with its trace normalization. -/
def inverseAdjointHilbertSchmidtNorm (A : Matrix.GeneralLinearGroup I ℂ) : ℝ :=
  Real.sqrt (inverseAdjointHilbertSchmidtSq A)

theorem inverseAdjointHilbertSchmidtNorm_eq_trace (A : Matrix.GeneralLinearGroup I ℂ) :
    inverseAdjointHilbertSchmidtNorm A =
      Real.sqrt ((LinearMap.trace ℂ (EuclideanSpace ℂ (InverseAdjointIndex I))
        (star (inverseAdjointRepresentation A) * inverseAdjointRepresentation A).toLinearMap).re) := by
  rw [inverseAdjointHilbertSchmidtNorm, inverseAdjointHilbertSchmidtSq_eq_trace]

theorem inverseAdjointHilbertSchmidtNorm_sq (A : Matrix.GeneralLinearGroup I ℂ) :
    inverseAdjointHilbertSchmidtNorm A ^ 2 =
      1 + (∑ i, ∑ j, ‖A i j‖ ^ 2) + ∑ i, ∑ j, ‖A⁻¹ i j‖ ^ 2 := by
  rw [inverseAdjointHilbertSchmidtNorm,
    Real.sq_sqrt (inverseAdjointHilbertSchmidtSq_pos A).le,
    inverseAdjointHilbertSchmidtSq_eq]

theorem one_le_inverseAdjointHilbertSchmidtNorm (A : Matrix.GeneralLinearGroup I ℂ) :
    1 ≤ inverseAdjointHilbertSchmidtNorm A :=
  Real.one_le_sqrt.mpr (one_le_inverseAdjointHilbertSchmidtSq A)

theorem inverseAdjointHilbertSchmidtNorm_pos (A : Matrix.GeneralLinearGroup I ℂ) :
    0 < inverseAdjointHilbertSchmidtNorm A :=
  lt_of_lt_of_le zero_lt_one (one_le_inverseAdjointHilbertSchmidtNorm A)

theorem continuous_inverseAdjointHilbertSchmidtNorm :
    Continuous (inverseAdjointHilbertSchmidtNorm (I := I)) := by
  unfold inverseAdjointHilbertSchmidtNorm inverseAdjointHilbertSchmidtSq
  exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((continuous_apply j).comp ((continuous_apply i).comp
      continuous_inverseAdjointMatrix)).norm.pow 2)).sqrt

end Langlands.LinearAlgebra
