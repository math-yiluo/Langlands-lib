import Langlands.GroupScheme.Rational.RankOneParabolicCovering
import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveProof

/-! # Proof of actual relative-root rank-one factorization -/

universe u

namespace Langlands.GroupScheme

/-- **Relative-root rank-one factorization** over arbitrary fields, for
connected reductive groups and their actual maximal split tori. -/
theorem rootRankOneFactorization : RootRankOneFactorizationStatement.{u} :=
  rootRankOneFactorization_of_componentReductivity
    RelativeRoot.kernelCentralizerComponentReductive.{u}

end Langlands.GroupScheme
