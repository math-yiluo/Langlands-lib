import Langlands.Geometry.Building.UnramifiedValuationDescentStatement
import Langlands.Geometry.Building.ValuationBuildingApartmentAxiomsAssembly
import Langlands.Geometry.Building.SimplyConnectedFacetFixingProof

/-! # The apartment axioms for every compatible valuation class: proof -/

universe u

namespace Langlands.Geometry.Building

/-- **The apartment axioms for every compatible valuation class** (KP §9.5 and §9.6.6). For
every connected reductive group over a nonarchimedean local field, all valuation building data
satisfy V 7 and AS 2–AS 5. -/
theorem valuationBuildingApartmentAxioms : ValuationBuildingApartmentAxiomsStatement.{u} :=
  valuationBuildingApartmentAxioms_of_facetFixing simplyConnectedFacetFixing

end Langlands.Geometry.Building
