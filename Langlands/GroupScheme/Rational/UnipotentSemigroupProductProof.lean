import Langlands.GroupScheme.Rational.SolvableIntersectionProduct
import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedProof
import Langlands.GroupScheme.Rational.CentralVectorQuotientProof

/-! # The exact ordered-product theorem for unipotent groups -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- The exact algebraically closed unipotent ordered-product statement,
with all structural prerequisites discharged. -/
theorem unipotentSemigroupOrderedProduct : UnipotentSemigroupOrderedProductStatement.{u} :=
  unipotentSemigroupOrderedProduct_of_solvableIntersection
    Torus.solvableFixedContainmentConnected centralStableVectorSubgroup

end Langlands.GroupScheme.RelativeRoot
