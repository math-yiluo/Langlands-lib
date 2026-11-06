import Langlands.GroupScheme.Rational.InfiniteFieldStronglyRegularPointReduction
import Langlands.GroupScheme.Absolute.StronglyRegularTorusPointProof

/-! # Strongly regular rational points over infinite fields -/

universe u

namespace Langlands.GroupScheme

/-- Every connected reductive group over an infinite field has a rational point whose all-test
centralizer is a closed torus: the reduction to the algebraically closed case, applied to the
proof of that case. -/
theorem infiniteFieldStronglyRegularPoint :
    InfiniteFieldStronglyRegularPointStatement.{u} :=
  infiniteFieldStronglyRegularPointReduction algClosedStronglyRegularTorusPoint

end Langlands.GroupScheme
