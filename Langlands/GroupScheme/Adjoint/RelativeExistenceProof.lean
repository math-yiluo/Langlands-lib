import Langlands.GroupScheme.Reductive.RelativeCenterProof
import Langlands.GroupScheme.RelativeCentralMultiplicativeTypeQuotient

/-! # Affine full-centre quotients over arbitrary bases -/

universe u

namespace Langlands.GroupScheme

/-- Every reductive group scheme over an arbitrary base has an affine fppf
quotient by its full scheme-theoretic centre. -/
theorem relativeAdjointQuotientExistence :
    RelativeAdjointQuotientExistenceStatement.{u} :=
  relativeAdjointQuotientExistence_of_center_and_centralMultiplicativeTypeQuotients
    reductiveRelativeCenter relativeCentralMultiplicativeTypeQuotient

end Langlands.GroupScheme
