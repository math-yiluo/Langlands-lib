import Langlands.GroupScheme.Rational.SolvableOrderedProductReduction
import Langlands.GroupScheme.Absolute.TriangularTorusConjugacy
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.SolvableSplitExtensionProof
import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedProof
import Langlands.GroupScheme.Rational.CentralVectorQuotientProof

/-! # Exact ordered semigroup products for solvable groups -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- CGP 3.3.11 with the exact cross-exclusion hypothesis, over every field
and at every universe, with all structural prerequisites discharged. -/
theorem semigroupOrderedProduct : SemigroupOrderedProductStatement.{u} :=
  semigroupOrderedProduct_of_solvableStructuralInputs
    (solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient
      solvableTorusQuotient solvableSplitExtension)
    Torus.solvableFixedContainmentConnected centralStableVectorSubgroup

end Langlands.GroupScheme.RelativeRoot
