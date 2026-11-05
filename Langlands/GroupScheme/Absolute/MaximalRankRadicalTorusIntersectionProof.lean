import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionOfQuotient
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Radical intersections in connected subgroups of maximal rank -/

universe u

namespace Langlands.GroupScheme

/-- In a smooth connected closed subgroup of maximal rank of a connected reductive group over
an algebraically closed field, the scheme-theoretic intersection of the specified maximal torus
with a solvable radical is a maximal torus of the radical. -/
theorem maximalRankRadicalTorusIntersection :
    MaximalRankRadicalTorusIntersectionStatement.{u} :=
  maximalRankRadicalTorusIntersectionStatement_of_solvableTorusQuotient solvableTorusQuotient

end Langlands.GroupScheme
