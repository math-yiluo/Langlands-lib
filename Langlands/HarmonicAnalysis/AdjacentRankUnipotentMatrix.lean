import Langlands.Representation.RankinSelberg.AdjacentRankStarData
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentFourier

/-! Actual matrix and phase identities for the adjacent-rank rectangular transform. -/

noncomputable section

open scoped BigOperators

namespace Langlands.HarmonicAnalysis

open GeneralLinear RankinSelberg

universe uK

variable {K : Type uK} [Field K]

/-- The square block obtained by the actual right action of `w * zeta` on `[u,y]`. -/
def adjacentRankLeftMatrix (r : ℕ) (u : upperUnipotent (r + 1) K)
    (y : Fin (r + 1) → K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  fun i j => Fin.cases (-y i) (fun k : Fin r => -u.val.val i k.rev.succ) j

@[simp] theorem adjacentRankLeftMatrix_zero (r : ℕ)
    (u : upperUnipotent (r + 1) K) (y : Fin (r + 1) → K) (i : Fin (r + 1)) :
    adjacentRankLeftMatrix r u y i 0 = -y i := by
  simp [adjacentRankLeftMatrix]

@[simp] theorem adjacentRankLeftMatrix_succ (r : ℕ)
    (u : upperUnipotent (r + 1) K) (y : Fin (r + 1) → K)
    (i : Fin (r + 1)) (j : Fin r) :
    adjacentRankLeftMatrix r u y i j.succ = -u.val.val i j.rev.succ := by
  simp [adjacentRankLeftMatrix]

private theorem matrix_mul_weyl_entry {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n) :
    (X * (weylLong n K).val) i j = X i j.rev := by
  classical
  change (∑ k, X i k * weylLong n K k j) = X i j.rev
  simp [weylLong_entry, mul_ite]

private theorem weyl_mul_matrix_entry {m n : ℕ}
    (X : Matrix (Fin n) (Fin m) K) (i : Fin n) (j : Fin m) :
    ((weylLong n K).val * X) i j = X i.rev j := by
  classical
  change (∑ k, weylLong n K i k * X k j) = X i.rev j
  simp [weylLong_entry, Fin.rev_eq_iff, ite_mul]

/-- Reversal sends the actual last basis column to the first basis column. -/
theorem adjacentRank_weyl_mulVec_epsilon (r : ℕ) :
    (weylLong (r + 1) K).val.mulVec (adjacentRankEpsilon K r) = Pi.single 0 1 := by
  classical
  ext i
  simp [adjacentRankEpsilon, Matrix.mulVec_single, weylLong_entry, Pi.single_apply, eq_comm]

/-- The first column of every actual upper-unipotent matrix is the first basis column. -/
theorem adjacentRank_unipotent_firstColumn (r : ℕ) (u : upperUnipotent (r + 1) K) :
    (fun i => u.val.val i 0) = Pi.single 0 1 := by
  classical
  ext i
  by_cases hi : i = 0
  · subst i
    simp [UpperUnipotent.entry_diag]
  · have hlt : (0 : Fin (r + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
    simpa [Pi.single_apply, hi, Ne.symm hi] using UpperUnipotent.entry_eq_zero u hlt

/-- The literal JPSS right action, including every minus sign and the final basis column. -/
theorem adjacentRankLeftMatrix_join (r : ℕ) (u : upperUnipotent (r + 1) K)
    (y : Fin (r + 1) → K) :
    rectangularJoin (adjacentRankLeftMatrix r u y)
      ((weylLong (r + 1) K).val.mulVec (adjacentRankEpsilon K r)) =
      rectangularJoin u.val.val y *
        (weylLong (r + 2) K * adjacentRankZeta K r).val := by
  classical
  have he (i : Fin (r + 1)) :
      ((weylLong (r + 1) K).val.mulVec (adjacentRankEpsilon K r)) i =
        u.val.val i 0 := by
    rw [adjacentRank_weyl_mulVec_epsilon, ← adjacentRank_unipotent_firstColumn r u]
  ext i j
  change _ = (rectangularJoin u.val.val y *
    ((weylLong (r + 2) K).val * (adjacentRankZeta K r).val)) i j
  rw [← Matrix.mul_assoc, adjacentRankZeta_val, Matrix.mul_diagonal]
  simp only [matrix_mul_weyl_entry]
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [rectangularJoin_last, Fin.rev_last, adjacentRankZetaDiagonal_last, mul_one, he]
    change u.val.val i 0 = rectangularJoin u.val.val y i (0 : Fin (r + 1)).castSucc
    rw [rectangularJoin_castSucc]
  · rw [rectangularJoin_castSucc, adjacentRankZetaDiagonal_castSucc, mul_neg_one,
      Fin.rev_castSucc]
    refine Fin.cases ?_ (fun l => ?_) k
    · simp only [adjacentRankLeftMatrix_zero, Fin.rev_zero, Fin.succ_last,
        rectangularJoin_last]
    · simp only [adjacentRankLeftMatrix_succ, Fin.rev_succ, ← Fin.castSucc_succ,
        rectangularJoin_castSucc]

/-- The left antidiagonal phase is the negative last coordinate minus the Whittaker sum. -/
theorem adjacentRankLeftMatrix_antiTrace (r : ℕ) (u : upperUnipotent (r + 1) K)
    (y : Fin (r + 1) → K) :
    (∑ i, adjacentRankLeftMatrix r u y i i.rev) =
      -y (Fin.last r) - unipotentFourierSum r u := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.rev_castSucc, adjacentRankLeftMatrix_succ, Fin.rev_rev,
    Fin.rev_last, adjacentRankLeftMatrix_zero, Finset.sum_neg_distrib,
    unipotentFourierSum]
  ring

/-- The shifted antidiagonal phase of the reversed unipotent matrix is the Whittaker sum. -/
theorem adjacentRank_weyl_shiftedAntiTrace (r : ℕ) (u : upperUnipotent (r + 1) K) :
    (∑ i : Fin r, ((weylLong (r + 1) K).val * u.val.val) i.succ i.rev.succ) =
      unipotentFourierSum r u := by
  simp only [weyl_mul_matrix_entry, Fin.rev_succ, unipotentFourierSum]
  exact Equiv.sum_comp Fin.revPerm (fun i : Fin r => u.val.val i.castSucc i.succ)

end Langlands.HarmonicAnalysis
