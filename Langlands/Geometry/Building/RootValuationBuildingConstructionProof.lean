import Langlands.Geometry.Building.RootValuationBuildingConstructionStatement
import Langlands.Geometry.Building.RootValuationBuildingConstructionReduction
import Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceProof
import Langlands.Geometry.Building.ActualApartmentSplittingProof
import Langlands.Geometry.Building.AffineIwahoriTitsProof
import Langlands.Geometry.Building.AffineIwahoriTitsBuildingProof

/-! # Actual root-valuation data with the metric-construction axioms: proof -/

universe u

namespace Langlands.Geometry.Building

/-- **The root-valuation building with its five axiom families** (KP Theorem 9.2.7, §9.5,
Theorem 9.6.5 and §9.6.6). For every connected reductive group over a nonarchimedean local
field there are parahoric building data, a polysimplicial realization and an apartment
splitting satisfying KP Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9. -/
theorem rootValuationBuildingConstruction : RootValuationBuildingConstructionStatement.{u} :=
  rootValuationBuildingConstructionReduction valuationApartmentAxiomsExistence
    actualApartmentSplitting affineIwahoriTits affineIwahoriTitsBuilding

end Langlands.Geometry.Building
