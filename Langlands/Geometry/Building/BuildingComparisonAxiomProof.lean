import Langlands.Geometry.Building.BuildingComparisonAxiomStatement
import Langlands.Geometry.Building.ValuationBuildingCentralSurjectionComparison

/-! # Proof of the comparisons of KP Axiom 4.1.1 for all supplied valuation data -/

noncomputable section

universe u

namespace Langlands.Geometry.Building

/-- **KP Axiom 4.1.1, comparison clauses.** For arbitrary valuation-building data on both
sides, central surjections, derived subgroups and simply connected covers of derived
subgroups induce equivariant isomorphisms of the reduced buildings. -/
theorem buildingComparisonAxiom : BuildingComparisonAxiomStatement.{u} := by
  intro F _ _ _ _
  exact ⟨fun G G' _ _ f hf B B' =>
      ValuationBuildingData.exists_isEquivariantBuildingIso_centralSurjection f hf B B',
    fun G Gder _ _ d hd B B' =>
      ValuationBuildingData.exists_isEquivariantBuildingIso_derivedSubgroup d hd B B',
    fun G Gder Gsc _ _ d π hdπ B B' =>
      ValuationBuildingData.exists_isEquivariantBuildingIso_simplyConnectedCover d π hdπ B B'⟩

end Langlands.Geometry.Building
