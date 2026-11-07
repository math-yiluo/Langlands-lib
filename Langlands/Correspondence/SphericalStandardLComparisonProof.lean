import Langlands.Correspondence.SphericalStandardLPrerequisites
import Langlands.Correspondence.SphericalTemperedStandardModuleProof
import Langlands.Correspondence.OrderedUnramifiedPrincipalSeriesLPolynomialProof

/-! # The standard L-polynomial of every spherical class -/

namespace Langlands.Correspondence

universe uF uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A supplied Langlands-defined standard L-polynomial on a spherical class is
the Euler polynomial of its spherical spectrum. -/
theorem sphericalStandardLComparison :
    SphericalStandardLComparisonStatement.{uF, uA} F :=
  sphericalStandardLComparison_of_prerequisites.{uF, uA} F
    (sphericalTemperedStandardModule.{uF, uA} F)
    (orderedUnramifiedPrincipalSeriesLPolynomial.{uF} F)

end Langlands.Correspondence
