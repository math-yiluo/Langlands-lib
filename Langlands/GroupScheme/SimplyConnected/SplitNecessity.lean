import Langlands.GroupScheme.SimplyConnected.SplitNecessityAssembly
import Langlands.GroupScheme.Reductive.SplitExistence
import Langlands.GroupScheme.Reductive.SplitCentralIsogenyExistenceProof
import Langlands.GroupScheme.Reductive.SplitSemisimplicity

/-!
# The coroot criterion for simple connectedness (necessity)

Unconditional proof of `SplitSimplyConnectedCorootSpanStatement`, obtained by applying the
conditional assembly `splitSimplyConnectedCorootSpan_of_inputs` to the proofs of its three
inputs.
-/

universe u

namespace Langlands.GroupScheme

/-- **Coroot criterion, necessity** (Milne, *Algebraic Groups*, Proposition 23.59, split case).
For an algebraically simply connected group over a field with a split maximal torus and a finite
reduced root datum of it, the coroots span the full cocharacter lattice over `ℤ`. -/
theorem splitSimplyConnectedCorootSpan : SplitSimplyConnectedCorootSpanStatement.{u} :=
  splitSimplyConnectedCorootSpan_of_inputs
    ⟨splitReductiveExistence, splitCentralIsogenyExistence, splitSemisimpleRootDatum⟩

end Langlands.GroupScheme
