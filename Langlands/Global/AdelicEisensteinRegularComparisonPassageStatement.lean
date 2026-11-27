import Langlands.Global.AdelicEisensteinFunctionalEquationRegularComparisonStatement
import Langlands.Global.AdelicEisensteinStandardFamilyComparisonStatement
import Langlands.Global.AdelicEisensteinRegularityPresentationComparisonStatement
import Langlands.Geometry.Building.BruhatTitsAvailabilityStatement

/-! # The regular-patch comparison from the standard family comparison -/

universe u

namespace Langlands.Global

/-- Bruhat–Tits availability, the regular-patch comparison for finite families in standard
position and the comparison of regularity across root presentations of one parabolic together
imply the regular-patch comparison for arbitrary parabolics, root presentations, Weyl
conjugations and maximal compact Iwasawa subgroups. -/
def EisensteinRegularComparisonPassageStatement : Prop :=
  Langlands.Geometry.Building.BruhatTitsAvailabilityStatement.{u} →
    StandardEisensteinFamilyComparisonStatement.{u} →
    RootPresentationRegularityComparisonStatement.{u} →
    EisensteinFunctionalEquationRegularComparisonStatement.{u}

end Langlands.Global
