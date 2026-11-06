import Langlands.GroupScheme.Rational.StandardParabolicEndpointsNegation
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # The endpoints of standard parabolics -/

universe u

namespace Langlands.GroupScheme

/-- For a connected reductive group over a field, a maximal split torus `i` and a generic
cocharacter `ν`, the empty-index standard parabolic and Levi are the dynamic parabolic of `ν`
and the centralizer of the torus, and at the full simple-root index the standard parabolic and
Levi are everything and the standard unipotent subgroup functor is trivial. -/
theorem standardParabolicEndpoints : StandardParabolicEndpointsStatement.{u} :=
  standardParabolicEndpoints_of_relativeRootNegation relativeRootNegation

end Langlands.GroupScheme
