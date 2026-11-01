import Langlands.HarmonicAnalysis.RectangularFourier
import Langlands.Representation.Shahidi.TwoBlocks
import Langlands.Group.GL.OppositeBlocks
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa

/-! Algebra of the exact ordered adjacent-rank lower parabolic. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Matrix

universe uF uV

/-- The host's exact ordered shape `(r+1,1)` in ambient rank `r+2`. -/
abbrev adjacentRankLowerShape (r : ℕ) : GeneralLinear.BlockShape (r + 2) :=
  Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)

section Algebra

variable {K : Type uF} [Field K] {r : ℕ}

/-- The large diagonal block of the actual lower parabolic. -/
def adjacentRankLowerLargeProjection :
    (adjacentRankLowerShape r).oppositeParabolic K →* GeneralLinear (r + 1) K where
  toFun p := (adjacentRankLowerShape r).oppositeLeviProjection K p 0
  map_one' := by simp; rfl
  map_mul' p q := by simp; rfl

@[simp] theorem adjacentRankLowerLargeProjection_apply
    (p : (adjacentRankLowerShape r).oppositeParabolic K) (i j : Fin (r + 1)) :
    adjacentRankLowerLargeProjection p i j = p.val i.castSucc j.castSucc := by
  change p.val ((adjacentRankLowerShape r).index 0 i)
    ((adjacentRankLowerShape r).index 0 j) = _
  simp only [adjacentRankLowerShape,
    Shahidi.twoBlocks_index_first (Nat.succ_pos r) (Nat.succ_pos 0)]
  rfl

theorem adjacentRankLower_upperRight_zero
    (p : (adjacentRankLowerShape r).oppositeParabolic K) (i : Fin (r + 1)) :
    p.val i.castSucc (Fin.last (r + 1)) = 0 := by
  have hp := (adjacentRankLowerShape r).mem_oppositeParabolic_iff K p.val |>.mp p.property
  have hz := hp 0 1 i (0 : Fin 1) (by change (0 : Fin 2) < 1; decide)
  simp only [adjacentRankLowerShape,
    Shahidi.twoBlocks_index_first (Nat.succ_pos r) (Nat.succ_pos 0),
    Shahidi.twoBlocks_index_second (Nat.succ_pos r) (Nat.succ_pos 0)] at hz
  have he : (0 : Fin 1).natAdd (r + 1) = Fin.last (r + 1) := by
    apply Fin.ext
    simp
  have hf : i.castAdd 1 = i.castSucc := by apply Fin.ext; rfl
  simpa only [he, hf] using hz

/-- The exact rectangular matrix identity needed by compact-average covariance. -/
theorem adjacentRankLower_rectangular_mul
    (p : (adjacentRankLowerShape r).oppositeParabolic K) (h : GeneralLinear (r + 1) K) :
    rectangularJoin h.val 0 * p.val.val =
      rectangularJoin (h * adjacentRankLowerLargeProjection p).val 0 := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, adjacentRankLower_upperRight_zero]
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

/-- The ambient determinant is the product of the two actual diagonal determinants. -/
theorem adjacentRankLower_determinant
    (p : (adjacentRankLowerShape r).oppositeParabolic K) :
    GeneralLinear.determinant p.val =
      GeneralLinear.determinant (adjacentRankLowerLargeProjection p) *
        GeneralLinear.determinant ((adjacentRankLowerShape r).oppositeLeviProjection K p 1) := by
  rw [TwoBlockConvergence.determinant_oppositeParabolic, Fin.prod_univ_two]
  rfl

end Algebra

end Langlands.RankinSelberg
