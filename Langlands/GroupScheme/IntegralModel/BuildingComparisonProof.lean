import Langlands.GroupScheme.IntegralModel.BuildingComparison
import Langlands.GroupScheme.IntegralModel.BuildingComparisonUnramifiedReduction
import Langlands.Geometry.Building.RootValuationBuildingConstructionProof
import Langlands.GroupScheme.IntegralModel.UnramifiedSpecialStabilizerProof
import Langlands.Geometry.Building.UnramifiedApartmentDescentProof

/-! # A geometric comparison for supplied reductive integral models: proof -/

universe u

namespace Langlands.GroupScheme.IntegralModel

/-- **The building comparison for supplied reductive integral models.** For every connected
reductive group over a nonarchimedean local field and every integral model with connected
reductive special fibre, the root-valuation building carries the comparison data: a complete
nonpositively curved metric with isometric continuous action, and a special vertex whose
compact stabilizer is the image of the integral points and which is the only point that image
fixes. -/
theorem buildingComparison : BuildingComparisonStatement.{u} :=
  buildingComparisonStatement_of_unramified
    Langlands.Geometry.Building.rootValuationBuildingConstruction unramifiedSpecialStabilizer
    (Langlands.Geometry.Building.unramifiedBuildingDescentStatement_of_apartmentDescent
      Langlands.Geometry.Building.unramifiedApartmentDescent)

end Langlands.GroupScheme.IntegralModel
