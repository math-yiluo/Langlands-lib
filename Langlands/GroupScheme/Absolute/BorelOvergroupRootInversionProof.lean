import Langlands.GroupScheme.Absolute.BorelOvergroupRootInversion

/-!
# Proof of `Langlands.GroupScheme.AbsoluteBorelOvergroupRootInversionStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Proof of `AbsoluteBorelOvergroupRootInversionStatement`. -/
theorem absoluteBorelOvergroupRootInversion : AbsoluteBorelOvergroupRootInversionStatement.{u} := by
  intro k _ _ G _ _ _ hG T hT j hj P _ _ i hi t ht α hα hp hm
  exact AbsoluteBorelOvergroup.exists_supportPreserving_weylInverter_of_both_signs
    hG hT j hj i hi t ht α hα hp hm

end Langlands.GroupScheme
