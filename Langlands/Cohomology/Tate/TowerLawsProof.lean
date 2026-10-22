import Langlands.Cohomology.Tate.TowerStatement
import Langlands.Cohomology.Tate.TowerTransitivity

universe u

namespace Langlands.Tate

/-- The constructed subgroup maps satisfy the exact tower proposition. -/
theorem towerLaws : TowerLaws.{u} := by
  intro R G _ _ _ K H h _ _ _ _ _ _ A n
  exact ⟨restriction_trans h A n, corestriction_trans h A n⟩

end Langlands.Tate
