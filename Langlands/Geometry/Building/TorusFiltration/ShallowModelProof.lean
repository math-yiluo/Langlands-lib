import Langlands.Geometry.Building.TorusFiltration.Construction
import Langlands.Geometry.Building.TorusFiltration.StructuralStatements

/-! # Smooth connected models below depth one -/

noncomputable section

universe u

namespace Langlands.Geometry.Building

/-- A shallow term of the minimal congruent filtration has a smooth model
with geometrically connected fibres. -/
theorem minimalCongruentShallowModel : MinimalCongruentShallowModelStatement.{u} := by
  intro F _ _ _ _ T _ hT q _
  let M := minimalCongruentModel F T hT q
  exact ⟨M.val, M.property.1, M.property.2.1,
    M.property.2.2.trans (minimalCongruentPoints_of_lt_one F T hT q)⟩

end Langlands.Geometry.Building
