import Langlands.GroupScheme.SimplyConnected.SplitCorootSpanLineReduction
import Langlands.GroupScheme.Reductive.RootDatumExistenceIndependent
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellIndependentProof
import Langlands.GroupScheme.Reductive.SplitRootLieLineIndependentProof

/-! # Simple connectedness forces integral coroot generation, via rank-one central covers -/

universe u

namespace Langlands.GroupScheme

/-- **Coroot criterion, necessity** (Milne, *Algebraic Groups*, Proposition 23.59, split case),
with root-datum existence, the rank-one root cell and the root Lie lines supplied by their
proofs through rank-one central covers. -/
theorem splitSimplyConnectedCorootSpanIndependent :
    SplitSimplyConnectedCorootSpanStatement.{u} :=
  splitSimplyConnectedCorootSpan_of_corootSpanLineInputs
    ⟨rootDatumExistenceIndependent, splitRankOneRootCellIndependent,
      splitRootLieLine_independent⟩

end Langlands.GroupScheme
