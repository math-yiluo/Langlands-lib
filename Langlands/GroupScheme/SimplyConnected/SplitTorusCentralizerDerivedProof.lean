import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedAssembly
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonProof
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Derived.SemisimpleProof

/-! # Derived subgroups of split-torus centralizers in simply connected groups -/

universe u

namespace Langlands.GroupScheme

/-- In a simply connected group `G` over a field `k`, the derived subgroup of the centralizer
`M = Z_G(A)` of a split subtorus `A` is simply connected. -/
theorem splitTorusCentralizerDerivedSimplyConnected :
    SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} :=
  splitTorusCentralizerDerivedSimplyConnected_of_inputs
    dynamicCentralizerReductive derivedSubgroupSemisimple splitSimplyConnectedCorootSpan
    splitCorootSpanSimplyConnected splitTorusCentralizerDerivedCorootComparison
    (fun k _ G hG => isSimplyConnectedFieldExtension k (AlgebraicClosure k) G hG)

end Langlands.GroupScheme
