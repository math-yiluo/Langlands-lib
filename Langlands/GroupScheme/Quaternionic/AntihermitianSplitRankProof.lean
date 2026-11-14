import Langlands.GroupScheme.SimplyConnected.AntihermitianSymplecticSplitRankStatement
import Langlands.GroupScheme.Quaternionic.AntihermitianSplitRankUpper
import Langlands.GroupScheme.Quaternionic.AntihermitianSplitRankLower

/-! # The split rank of the symplectic group of an antihermitian form is its Witt index -/

universe u

namespace Langlands.GroupScheme

/-- For an invertible trace-valued `σ`-antihermitian Gram matrix `H ∈ M_m(D)`, the split rank of
`σ.symplecticGroup H` is the Witt index of `H`. The degree hypotheses of the statement are not
used. -/
theorem antihermitianSymplecticSplitRank : AntihermitianSymplecticSplitRankStatement.{u} := by
  intro K _ D _ _ _ _ degree m _ σ H _ _ hH hu
  exact le_antisymm (AntihermitianSplitRank.splitRank_le_wittIndex σ H hu)
    (AntihermitianSplitRank.wittIndex_le_splitRank σ H hH hu)

end Langlands.GroupScheme
