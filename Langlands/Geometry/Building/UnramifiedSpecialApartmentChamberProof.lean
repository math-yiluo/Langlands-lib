import Langlands.Geometry.Building.UnramifiedSpecialApartmentChamberStatement
import Langlands.Geometry.Building.UnramifiedSpecialApartmentArithmeticReduction
import Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof

/-! # Ordinary coefficient-stable chambers in every supplied special apartment -/

universe u

namespace Langlands.Geometry.Building

/-- Every supplied compatible coefficient-stable special apartment contains a
regular point whose entire ordinary sign facet is coefficient-stable. -/
theorem unramifiedSpecialApartmentChamber :
    UnramifiedSpecialApartmentChamberStatement.{u} :=
  unramifiedSpecialApartmentChamber_of_connectedGeneration.{u}
    Langlands.GroupScheme.connectedGeneration.{u}

end Langlands.Geometry.Building
