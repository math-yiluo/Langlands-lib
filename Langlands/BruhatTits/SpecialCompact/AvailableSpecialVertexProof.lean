import Langlands.BruhatTits.SpecialCompact.AvailableSpecialVertexStatement
import Langlands.Geometry.Building.SpecialPointExistence
import Langlands.Geometry.Building.SpecialPointVertices

/-! # A special vertex in the apartment of available corrected KP data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- The apartment of available corrected KP data contains a special vertex. -/
theorem availableSpecialVertexExistence : AvailableSpecialVertexExistenceStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅
  have hΨ := h𝔅.affineRootSystem.apartmentAxioms.isAffineRootSystem_affineRoots
  obtain ⟨x, hx⟩ := hΨ.exists_isSpecialPoint
  exact ⟨x, hx, AffineRootSystem.isVertex_of_isSpecialPoint hΨ hx⟩

end Langlands.BruhatTits.SpecialCompact
