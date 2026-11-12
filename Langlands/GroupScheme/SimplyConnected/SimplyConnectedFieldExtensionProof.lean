import Langlands.GroupScheme.SimplyConnected.FieldExtensionStructuralAssembly
import Langlands.GroupScheme.SimplyConnected.SplitNecessityAssembly
import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceProof
import Langlands.GroupScheme.SimplyConnected.UniversalPropertyProof
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.GroupScheme.Descent.TensorFullCoverProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitExistence
import Langlands.GroupScheme.Reductive.SplitCentralIsogenyExistenceProof
import Langlands.GroupScheme.Reductive.SplitSemisimplicity

/-! # Simple connectedness is preserved by arbitrary field extension -/

universe u

namespace Langlands.GroupScheme

/-- **Simple connectedness ascends along field extensions** (CGP, Corollary A.4.11(1)). For
every field extension `K/k` and every simply connected semisimple `k`-group `G`, the base change
`G_K` is simply connected. -/
theorem isSimplyConnectedFieldExtension : IsSimplyConnectedFieldExtensionStatement.{u} :=
  isSimplyConnectedFieldExtension_of_descent_and_splitStructure
    simplyConnectedCoverTensorDescent splitSimplyConnectedCoverExistence
    simplyConnectedCentralCoverUniversalProperty maximalTorusBaseChange rootDatumExistence
    (splitSimplyConnectedCorootSpan_of_inputs
      ⟨splitReductiveExistence, splitCentralIsogenyExistence, splitSemisimpleRootDatum⟩)
    splitCorootSpanSimplyConnected

end Langlands.GroupScheme
