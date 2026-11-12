import Langlands.Geometry.Building.FullValidity.DatumTransportProof
import Langlands.BruhatTits.SpecialCompact.AssignmentRebasingConstruction

/-! # Rebasing a valid corrected KP assignment at a prescribed maximal split torus -/

universe u

namespace Langlands.BruhatTits.SpecialCompact

open Langlands.Geometry.Building

/-- A valid corrected KP assignment can be rebased at any prescribed maximal split torus. -/
theorem validAssignmentTorusRebasing : ValidAssignmentTorusRebasingStatement.{u} := by
  intro B hB F instField instValuation instTopology instLocal G hG S i hi
  let result := rebaseAssignmentFromDatumTransport
    kpBuildingDatumTransportStatement B hB F G hG S i hi
  exact ⟨result.val, result.property⟩

end Langlands.BruhatTits.SpecialCompact
