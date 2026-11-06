import Langlands.GroupScheme.Reductive.FixedCenterContainingTorusSemidirect
import Langlands.GroupScheme.AutomorphicAction.SemidirectReductive
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # A fixed split torus containing the full centre -/

universe u

namespace Langlands.GroupScheme

/-- The fixed-centre target follows from the algebraically closed case of the
self-centralization of maximal tori, since semidirect products of a connected
reductive group by a split torus are connected reductive. -/
theorem fixedCenterContainingTorus_of_algClosedMaximalTorusCentralizer
    (hcent : AlgClosedMaximalTorusCentralizerStatement.{u}) :
    FixedCenterContainingTorusStatement.{u} :=
  fixedCenterContainingTorusSemidirectReduction hcent
    (fun _ _ _ _ hG _ hS b => b.isConnectedReductive_semidirectProduct_of_isAlgClosed hS hG)

/-- Over an algebraically closed field, a split-torus action on a connected
reductive group fixes a closed split torus containing the whole centre. -/
theorem fixedCenterContainingTorus : FixedCenterContainingTorusStatement.{u} :=
  fixedCenterContainingTorus_of_algClosedMaximalTorusCentralizer
    (algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
      solvableTorusQuotient)

end Langlands.GroupScheme
