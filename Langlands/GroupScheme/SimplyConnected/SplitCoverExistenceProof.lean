import Langlands.GroupScheme.SimplyConnected.SplitCoverMinimalLattice
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof
import Langlands.GroupScheme.Derived.SemisimplePerfectProof

/-! # Simply connected central covers of split semisimple groups -/

universe u

namespace Langlands.GroupScheme

/-- **Simply connected central covers of split semisimple groups** (Milne Remark 23.60, split
case). Every semisimple group over a field with a split maximal torus has a central isogeny from
a simply connected group. -/
theorem splitSimplyConnectedCoverExistence : SplitSimplyConnectedCoverExistenceStatement.{u} :=
  splitSimplyConnectedCoverExistence_of_minimalLattice rootDatumExistence
    centralIsogenyRootDatumHom semisimplePerfect

end Langlands.GroupScheme
