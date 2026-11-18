import Langlands.GroupScheme.Rational.NormalSubgroupTorusIntersection
import Langlands.GroupScheme.Rational.NormalSubgroupParabolicIntersection
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupSelfNormalizerProof

/-! # Normal subgroups meet maximal tori, parabolic and Borel subgroups well: proof -/

universe u

namespace Langlands.GroupScheme

/-- Conrad, *Reductive group schemes*, Exercise 5.5.1. For a smooth connected affine group `G`
over a field: the intersection of a maximal torus with a smooth connected closed subgroup that
it normalizes is a maximal torus of that subgroup; the intersection of a parabolic subgroup with
a smooth connected closed normal subgroup `H` is a connected parabolic subgroup of `H`; and the
intersection of a geometric Borel subgroup with `H` is a geometric Borel subgroup of `H`. -/
theorem normalSubgroupIntersection : NormalSubgroupIntersectionStatement.{u} :=
  NormalSubgroupParabolicIntersection.normalSubgroupIntersection_of_torusClause_of_borelSelfNormalizer
    borelContainingSubgroupSelfNormalizer
    (fun _ _ G _ _ _ T t ht N n hn hNs hNc hnorm =>
      NormalSubgroupIntersection.torusIntersection G T t ht N n hn hNs hNc hnorm)

end Langlands.GroupScheme
