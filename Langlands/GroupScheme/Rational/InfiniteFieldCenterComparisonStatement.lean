import Langlands.GroupScheme.Rational.RationalCenterComparisonStatement

/-! # The center on rational points over an infinite field -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a connected reductive group over an infinite field, the rational points
of the full scheme center equal the center of the group of rational points. -/
def InfiniteFieldCenterComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → RationalCenterComparison G

end Langlands.GroupScheme
