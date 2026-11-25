import Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement
import Langlands.Geometry.Building.UnramifiedValuationDescentStatement
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.UnramifiedValuationDescentProof
import Langlands.Geometry.Building.ValuationBuildingApartmentAxiomsProof

/-! # Existence of actual valuation data satisfying the Chapter 7 apartment axioms: proof -/

universe u

namespace Langlands.Geometry.Building

/-- **Valuation data satisfying the apartment axioms exist** (KP §9.6, Theorem 9.6.5, with
§9.5 and §9.6.6). For every connected reductive group over a nonarchimedean local field there
are valuation building data satisfying V 6, V 7 and AS 2–AS 5. -/
theorem valuationApartmentAxiomsExistence : ValuationApartmentAxiomsExistenceStatement.{u} :=
  valuationApartmentAxiomsExistenceReduction
    (unramifiedQuasiSplit_of_henselianDiscrete Langlands.GroupScheme.henselianDiscreteQuasiSplit)
    quasiSplitIntegerApartmentExistence specialTorusExistence unramifiedValuationDescent
    valuationBuildingApartmentAxioms

end Langlands.Geometry.Building
