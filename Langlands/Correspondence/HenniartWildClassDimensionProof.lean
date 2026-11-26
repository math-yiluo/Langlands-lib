import Langlands.Correspondence.HenniartWildClassDimension
import Langlands.Correspondence.HenniartWildInertia

/-!
# Dimensions of irreducible representations of wild inertia: proof
-/

namespace Langlands.Henniart

universe uK uW

/-- Irreducible representations of wild inertia with open kernel have `p`-power dimension. -/
theorem wildClassRankPrimePower : WildClassRankPrimePowerStatement.{uK, uW} := by
  intro p _ K c
  exact (WildInertia.pPowerOpen_weilWildInertia K).rank c

end Langlands.Henniart
