import Langlands.GroupScheme.Quaternionic.LineRotation
import Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryProof
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # The split matrix of a quaternionic line rotation -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

open FirstKindInvolution MoritaIsometry FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  {L : Type u} [Field L] [Algebra F L] (e : L ⊗[F] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) {n : ℕ}

/-- The split matrix of a rank-one update has rank at most two. -/
theorem rank_chartN_vecMulVec (a b : Fin n → L ⊗[F] D) :
    (chartN e n L ((coefficientEquiv F D L).symm (vecMulVec a b))).rank ≤ 2 := by
  let A : Matrix (Fin n × Fin 2) (Fin 2) L := Matrix.of fun p γ => chartR e L (a p.1) p.2 γ
  let B : Matrix (Fin 2) (Fin n × Fin 2) L := Matrix.of fun γ p => chartR e L (b p.1) γ p.2
  have h : matrixChartR e L ((coefficientEquiv F D L).symm (vecMulVec a b)) = A * B := by
    ext ⟨i, α⟩ ⟨j, β⟩
    rw [matrixChartR_apply, AlgEquiv.apply_symm_apply, vecMulVec_apply, _root_.map_mul]
    simp [Matrix.mul_apply, A, B]
  rw [chartN_apply, Matrix.rank_reindex, h]
  exact (Matrix.rank_mul_le_left A B).trans ((Matrix.rank_le_card_width A).trans (by simp))

variable (σ : FirstKindInvolution F D) (q : σ.QuadraticForms (Fin n)) (x : Fin n → D)

/-- The split matrix of a line rotation differs from the identity by a matrix of rank at most
two. -/
theorem rank_chartN_lineRotationMatrix_sub_one (t : L ⊗[F] D) :
    (chartN e n L ((coefficientEquiv F D L).symm (σ.lineRotationMatrix q x L t)) - 1).rank ≤
      2 := by
  rw [lineRotationMatrix, _root_.map_sub, _root_.map_one, _root_.map_sub, _root_.map_one,
    sub_sub_cancel_left]
  set X := chartN e n L ((coefficientEquiv F D L).symm
    (vecMulVec (σ.lineColumn q x L) (σ.lineRow q x L t)))
  rw [show -X = X * -1 by rw [mul_neg, mul_one]]
  exact (Matrix.rank_mul_le_left X (-1)).trans (rank_chartN_vecMulVec e _ _)

end Langlands.GroupScheme.Quaternionic
