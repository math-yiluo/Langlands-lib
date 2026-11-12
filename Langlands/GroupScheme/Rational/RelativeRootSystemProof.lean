import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.Rational.RootSystemFromFactorPairs
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Proof of the relative root system -/

universe u

namespace Langlands.GroupScheme

/-- **The relative root system** (Milne 25.16–25.17, Borel–Tits 5.8, by the
Conrad–Gabber–Prasad C.2.15 route). For a maximal split torus of a connected reductive
group over any field, the relative roots form a finite crystallographic, possibly
nonreduced root system on their rational span, and `N(k)/Z(k)` acts faithfully on that
span with image the Weyl group of this root system. -/
theorem relativeRootSystem : RelativeRootSystemStatement.{u} :=
  relativeRootSystemStatement_of_rootRankOneFactorizationStatement rootRankOneFactorization

end Langlands.GroupScheme
