import Langlands.GroupScheme.SimplyConnected.SplitCoverMinimalLattice
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof
import Langlands.GroupScheme.Derived.SemisimplePerfectProof

/-! # Simply connected central covers from root-datum existence

Conditional helper isolating the single root-datum input of split simply connected covers. -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Split simply connected covers from root-datum existence.** `RootDatumExistenceStatement`
implies `SplitSimplyConnectedCoverExistenceStatement`; the central-isogeny root-datum morphism
and perfectness of semisimple groups are supplied by `centralIsogenyRootDatumHom` and
`semisimplePerfect`. -/
theorem splitSimplyConnectedCoverExistence_of_rootDatumExistence
    (hRD : RootDatumExistenceStatement.{u}) :
    SplitSimplyConnectedCoverExistenceStatement.{u} :=
  splitSimplyConnectedCoverExistence_of_minimalLattice hRD centralIsogenyRootDatumHom
    semisimplePerfect

end Langlands.GroupScheme
