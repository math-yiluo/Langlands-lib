import Langlands.GroupScheme.Rational.RootGeneratedCentralizerRankOneReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Proof of rank-one generation of the root-generated centralizer part -/

universe u

namespace Langlands.GroupScheme

/-- **Rank-one generation of the root-generated part of a split-torus
centralizer** over arbitrary fields, for connected reductive groups and their
actual maximal split tori. -/
theorem rootGeneratedCentralizerRankOne : RootGeneratedCentralizerRankOneStatement.{u} :=
  rootGeneratedCentralizerRankOneReduction rootRankOneFactorization

end Langlands.GroupScheme
