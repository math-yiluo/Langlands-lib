import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterAssembly
import Langlands.GroupScheme.Rational.LeviCocenterRootModelProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity

/-! # Cocenters of split-torus centralizers in simply connected groups are induced (proof) -/

universe u

namespace Langlands.GroupScheme

/-- In a simply connected group over an arbitrary field, every commutative fppf quotient of the
centralizer of a split subtorus by its derived subgroup is an induced torus. -/
theorem splitTorusCentralizerCocenterInduced :
    SplitTorusCentralizerCocenterInducedStatement.{u} :=
  splitTorusCentralizerCocenterInduced_of_inputs
    ⟨dynamicCentralizerReductive, cocenterQuotientExistence, isSimplyConnectedFieldExtension,
      splitSimplyConnectedCorootSpan, splitTorusCentralizerCocenterRootModel⟩

end Langlands.GroupScheme
