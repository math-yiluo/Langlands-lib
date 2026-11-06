import Langlands.GroupScheme.Rational.StandardLeviTwistedIntersectionAssembly
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Twisted intersections of actual standard Levi subgroup functors: proof -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- The literal twisted standard-Levi intersection equality holds on every test
scheme, for every minimum double-coset representative and every normalizer lift. -/
theorem standardLeviTwistedIntersection :
    StandardLeviTwistedIntersectionStatement.{u} :=
  standardLeviTwistedIntersection_of_connected_of_negation dynamicConnected relativeRootNegation

end Langlands.GroupScheme
