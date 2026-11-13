import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Langlands.Geometry.Building.MaximalUnramifiedApartmentInjective
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof

/-! # Unramified building descent from its seven remaining inputs -/

universe u

namespace Langlands.Geometry.Building

/-- The seven inputs of `UnramifiedBuildingDescentReductionStatement` that are not yet proved
imply `UnramifiedBuildingDescentStatement`. The two other inputs,
`QuasiSplitIntegerApartmentExistenceStatement` and
`MaximalUnramifiedApartmentInjectiveStatement`, are proved. -/
def UnramifiedBuildingDescentRemainingReductionStatement : Prop :=
  UnramifiedQuasiSplitStatement.{u} →
  SpecialTorusExistenceStatement.{u} →
  UnramifiedValuationDescentStatement.{u} →
  ValuationBuildingApartmentAxiomsStatement.{u} →
  ChapterSevenBuildingAxiomsStatement.{u} →
  UnramifiedGaloisFixedBuildingPointStatement.{u} →
  UnramifiedSpecialPointDescentStatement.{u} →
  UnramifiedBuildingDescentStatement.{u}

/-- Proof of the refined reduction: supply the proved inputs
`quasiSplitIntegerApartmentExistence` and `maximalUnramifiedApartmentInjective` to
`unramifiedBuildingDescentReduction`. -/
theorem unramifiedBuildingDescentRemainingReduction :
    UnramifiedBuildingDescentRemainingReductionStatement.{u} :=
  fun hQS hSpec hDesc hAx hCh7 hFix hSpecial =>
    unramifiedBuildingDescentReduction hQS quasiSplitIntegerApartmentExistence hSpec hDesc hAx
      hCh7 maximalUnramifiedApartmentInjective hFix hSpecial

end Langlands.Geometry.Building
