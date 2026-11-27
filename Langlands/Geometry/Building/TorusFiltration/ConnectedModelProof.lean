import Langlands.Geometry.Building.TorusFiltration.Construction
import Langlands.Geometry.Building.TorusFiltration.StructuralStatements

/-! # Smooth connected models at every depth -/

noncomputable section

universe u

namespace Langlands.Geometry.Building

/-- The constructed minimal congruent filtration has smooth models with
geometrically connected fibres at every depth. -/
theorem minimalCongruentConnectedModel : MinimalCongruentConnectedModelStatement.{u} := by
  intro F _ _ _ _ T _ hT r
  let M := minimalCongruentModel F T hT r
  exact ⟨M.val, M.property⟩

end Langlands.Geometry.Building
