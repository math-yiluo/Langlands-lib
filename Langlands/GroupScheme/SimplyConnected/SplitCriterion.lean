import Langlands.GroupScheme.SimplyConnected.SplitCriterionReduction
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.CentralIsogeny.SplitMaximalTorusLiftProof
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof

/-!
# The coroot criterion for simple connectedness (sufficiency)

Unconditional proof of `SplitCorootSpanSimplyConnectedStatement`, obtained by applying the
conditional reduction `splitCorootSpanSimplyConnected_of_rootDatumHom` to the proofs of its
three premises.
-/

namespace Langlands.GroupScheme

universe u

/-- **Coroot criterion, sufficiency** (Milne, *Algebraic Groups*, Proposition 23.29). A
semisimple group over a field with a split maximal torus whose coroots span the cocharacter
lattice is simply connected. -/
theorem splitCorootSpanSimplyConnected : SplitCorootSpanSimplyConnectedStatement.{u} :=
  splitCorootSpanSimplyConnected_of_rootDatumHom
    rootDatumExistence
    centralIsogenySplitMaximalTorusLift
    centralIsogenyRootDatumHom

end Langlands.GroupScheme
