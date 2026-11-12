import Langlands.GroupScheme.Absolute.BorelOvergroupRankOne

/-!
# Proof of `Langlands.GroupScheme.AbsoluteBorelOvergroupRankOneContainmentStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Proof of `AbsoluteBorelOvergroupRankOneContainmentStatement`. -/
theorem absoluteBorelOvergroupRankOneContainment : AbsoluteBorelOvergroupRankOneContainmentStatement.{u} := by
  intro k _ G _ _ _ hG T hT j hj P _ _ i hi t ht α hα hp hm
  exact AbsoluteBorelOvergroup.rankOneCentralizer_le_range_of_both_signs
    hG hT j hj i hi t ht α hα hp hm

end Langlands.GroupScheme
