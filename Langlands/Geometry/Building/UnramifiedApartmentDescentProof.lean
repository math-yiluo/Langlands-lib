import Langlands.Geometry.Building.UnramifiedApartmentDescentStatement
import Langlands.Geometry.Building.UnramifiedApartmentDescentReduction
import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.UnramifiedValuationDescentProof
import Langlands.Geometry.Building.ValuationBuildingApartmentAxiomsProof
import Langlands.Geometry.Building.ChapterSevenBuildingAxiomsProof
import Langlands.Geometry.Building.UnramifiedGaloisFixedBuildingPointProof
import Langlands.Geometry.Building.UnramifiedAffineRootRestrictionProof

/-! # Apartment-compatible descent of the building from the maximal unramified extension:
proof -/

universe u

namespace Langlands.Geometry.Building

/-- **Apartment-compatible unramified descent of the building** (KP §§9.2–9.3, 9.6.6, 9.9.2).
For every connected reductive group over a nonarchimedean local field and all valuation building
data `B`, the building of `B` embeds `G(F)`-equivariantly and apartment-compatibly onto the
Galois-fixed points of the building over the maximal unramified extension, with the special
point, facet and torus clauses. -/
theorem unramifiedApartmentDescent : UnramifiedApartmentDescentStatement.{u} :=
  unramifiedApartmentDescentReduction specialTorusExistence unramifiedValuationDescent
    valuationBuildingApartmentAxioms chapterSevenBuildingAxioms unramifiedGaloisFixedBuildingPoint
    unramifiedAffineRootRestriction

end Langlands.Geometry.Building
