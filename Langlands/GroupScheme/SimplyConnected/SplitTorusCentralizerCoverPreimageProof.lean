import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageReduction
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedAssembly
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonProof
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof

/-! # The preimage of a split-torus centralizer in a simply connected cover -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Let `G` be connected reductive over a field, `π : C ⟶ D` a central isogeny from a simply
connected group onto the derived subgroup `D` of `G`, and `M` the centralizer of a split
subtorus of `G`. The preimage of `M` in `C` is the centralizer of a split subtorus of `C`, and
the restriction `M' ⟶ M` of `C ⟶ G` relates characters, derived subgroups and maximal tori as
in `SplitTorusCentralizerCoverPreimageStatement`. -/
theorem splitTorusCentralizerCoverPreimage :
    SplitTorusCentralizerCoverPreimageStatement.{u} :=
  splitTorusCentralizerCoverPreimage_of_inputs reductiveCentralDerivedProduct
    dynamicCentralizerReductive
    (splitTorusCentralizerDerivedSimplyConnected_of_inputs dynamicCentralizerReductive
      derivedSubgroupSemisimple splitSimplyConnectedCorootSpan splitCorootSpanSimplyConnected
      splitTorusCentralizerDerivedCorootComparison
      (fun k _ G hG => isSimplyConnectedFieldExtension k (AlgebraicClosure k) G hG))

end Langlands.GroupScheme
