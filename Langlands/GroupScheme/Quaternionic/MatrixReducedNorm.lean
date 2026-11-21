import Langlands.Algebra.CentralSimpleScalarExtension
import Langlands.GroupScheme.Quaternionic.DegreeSplittingMatrix

/-! # The reduced norm in quaternionic Gram coordinates -/

noncomputable section

open Matrix
open scoped TensorProduct

universe u

namespace Langlands.GroupScheme.Quaternionic

open FiniteAlgebraUnits.MatrixPoints Langlands.CentralSimple

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [FiniteDimensional K D]
  {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The actual reduced norm of a square matrix with coefficients in the scalar extension
  of a central division algebra. -/
def matrixReducedNorm (R : Type u) [CommRing R] [Algebra K R] :
    Matrix I I (R ⊗[K] D) →*₀ R :=
  (reducedNorm K (Matrix I I D) R).comp
    (MonoidWithZeroHom.ofClass (coefficientEquiv (m := I) K D R).symm)

/-- Coefficient change commutes with the reduced norm in matrix coordinates. -/
theorem matrixReducedNorm_naturality {R S : Type u} [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (f : R →ₐ[K] S) (A : Matrix I I (R ⊗[K] D)) :
    matrixReducedNorm S (A.map (Algebra.TensorProduct.map f (AlgHom.id K D))) =
      f (matrixReducedNorm R A) := by
  change reducedNorm K (Matrix I I D) S ((coefficientEquiv (m := I) K D S).symm (A.map _)) =
    f (reducedNorm K (Matrix I I D) R ((coefficientEquiv (m := I) K D R).symm A))
  rw [← reducedNorm_naturality K (Matrix I I D) f]
  congr 1
  apply (coefficientEquiv (m := I) K D S).injective
  rw [AlgEquiv.apply_symm_apply, coefficientEquiv_naturality, AlgEquiv.apply_symm_apply]

/-- A diagonal matrix has reduced norm the product of the reduced norms of its entries. -/
theorem matrixReducedNorm_diagonal (R : Type u) [CommRing R] [Algebra K R]
    (a : I → R ⊗[K] D) : matrixReducedNorm R (Matrix.diagonal a) = ∏ i, reducedNorm K D R (a i) := by
  let L := AlgebraicClosure K
  let e := algebraicClosureChart K D
  let S := L ⊗[K] R
  let f : R →ₐ[K] S := Algebra.TensorProduct.includeRight
  let F := Algebra.TensorProduct.map f (AlgHom.id K D)
  apply Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  change f _ = f _
  rw [← matrixReducedNorm_naturality f, map_prod]
  simp_rw [← reducedNorm_naturality K D f]
  rw [Matrix.diagonal_map (map_zero F)]
  change reducedNorm K (Matrix I I D) S
    ((coefficientEquiv (m := I) K D S).symm (Matrix.diagonal fun i => F (a i))) = _
  rw [DegreeSplitting.reducedNorm_eq_det_matrixChartR e]
  simp_rw [reducedNorm_eq_det K D e S, ← DegreeSplitting.chartR_apply]
  let M : Matrix (I × Fin (reducedDegree K D)) (I × Fin (reducedDegree K D)) S :=
    DegreeSplitting.matrixChartR e S ((coefficientEquiv (m := I) K D S).symm (Matrix.diagonal fun i => F (a i)))
  change M.det = _
  have hM : Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) M =
      Matrix.blockDiagonal (fun i => DegreeSplitting.chartR e S (F (a i))) := by
    ext ⟨p, i⟩ ⟨q, j⟩
    change M (i, p) (j, q) = _
    dsimp only [M]
    rw [DegreeSplitting.matrixChartR_apply, AlgEquiv.apply_symm_apply, Matrix.diagonal_apply,
      Matrix.blockDiagonal_apply]
    split_ifs
    · rfl
    · rw [_root_.map_zero]
      rfl
  rw [← Matrix.det_reindex_self (Equiv.prodComm _ _) M, hM, Matrix.det_blockDiagonal]

/-- The reduced norm is invariant under conjugate transpose for a first-kind involution. -/
theorem matrixReducedNorm_adjoint (R : Type u) [CommRing R] [Algebra K R]
    (τ : FirstKindInvolution K D) (A : Matrix I I (R ⊗[K] D)) :
    matrixReducedNorm R ((τ.baseChange R).matrix I A) = matrixReducedNorm R A := by
  let L := AlgebraicClosure K
  let e := algebraicClosureChart K D
  let S := L ⊗[K] R
  let f : R →ₐ[K] S := Algebra.TensorProduct.includeRight
  let X := (coefficientEquiv (m := I) K D R).symm A
  have hX : (coefficientEquiv (m := I) K D R).symm ((τ.baseChange R).matrix I A) = (τ.matrix I).baseChange R X := by
    apply (coefficientEquiv (m := I) K D R).injective
    rw [AlgEquiv.apply_symm_apply]
    ext i j
    rw [FirstKindInvolution.matrix_apply, FirstKindInvolution.coefficientEquiv_baseChange,
      show coefficientEquiv (m := I) K D R X = A from AlgEquiv.apply_symm_apply _ _]
  change reducedNorm K (Matrix I I D) R ((coefficientEquiv (m := I) K D R).symm _) =
    reducedNorm K (Matrix I I D) R X
  rw [hX]
  apply Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  change f _ = f _
  rw [← reducedNorm_naturality K (Matrix I I D) f, ← reducedNorm_naturality K (Matrix I I D) f,
    (τ.matrix I).map_baseChange, DegreeSplitting.reducedNorm_eq_det_matrixChartR e,
    DegreeSplitting.reducedNorm_eq_det_matrixChartR e, DegreeSplitting.matrixChartR_baseChange]
  let B := (DegreeSplitting.blockInvolutionMatrix (n := I) e τ).map (algebraMap L S)
  let C := (DegreeSplitting.blockInvolutionMatrixInv (n := I) e τ).map (algebraMap L S)
  have hBC : B * C = 1 := by
    dsimp only [B, C]
    rw [← Matrix.map_mul, DegreeSplitting.blockInvolutionMatrix_mul_inv]
    simp
  have hdet : B.det * C.det = 1 := by rw [← Matrix.det_mul, hBC, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_comm B.det, mul_assoc, hdet, mul_one]

/-- Reduced norms transform by a square under change of basis of a Gram matrix. -/
theorem matrixReducedNorm_congruence (R : Type u) [CommRing R] [Algebra K R]
    (τ : FirstKindInvolution K D) (A U : Matrix I I (R ⊗[K] D)) :
    matrixReducedNorm R (U * A * (τ.baseChange R).matrix I U) =
      matrixReducedNorm R A * (matrixReducedNorm R U) ^ 2 := by
  rw [map_mul, map_mul, matrixReducedNorm_adjoint, pow_two, mul_comm (matrixReducedNorm R U), mul_assoc]

end Langlands.GroupScheme.Quaternionic
