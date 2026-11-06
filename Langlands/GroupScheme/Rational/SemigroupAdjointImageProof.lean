import Langlands.GroupScheme.Rational.SemigroupComparisonFourPrerequisites
import Langlands.GroupScheme.Reductive.FixedCenterContainingTorusProof

/-! # Actual semigroup fppf images under adjoint quotients -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- An equivariant adjoint quotient induces an actual fppf image of semigroup
subgroups for every character semigroup containing zero. -/
theorem semigroupAdjointImage : SemigroupAdjointImageStatement.{u} :=
  semigroupAdjointImage_of_fixedCenterContainingTorus fixedCenterContainingTorus

end Langlands.GroupScheme.RelativeRoot
