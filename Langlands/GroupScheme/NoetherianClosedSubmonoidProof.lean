import Langlands.GroupScheme.NoetherianClosedSubmonoidStatement
import Langlands.GroupScheme.ImageGenerationSubgroup

/-! # Proof of closed submonoid recognition over an arbitrary base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.ImageGeneration

/-- A closed submonoid with Noetherian affine square is a closed subgroup, carried by
the submonoid itself. -/
theorem noetherianClosedSubmonoid : NoetherianClosedSubmonoidStatement.{u} := by
  intro B G Z j hj m hm e he hA hN
  have := hj
  have := hA
  have := hN
  exact ⟨closedSubgroup j m hm e he, closedSubgroupHom j m hm e he,
    isClosedSubgroup_closedSubgroupHom j m hm e he, Iso.refl Z,
    by rw [closedSubgroupHom_hom]; exact Category.id_comp j⟩

end Langlands.GroupScheme.ImageGeneration
