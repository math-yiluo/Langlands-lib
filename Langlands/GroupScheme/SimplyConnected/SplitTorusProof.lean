import Langlands.GroupScheme.SimplyConnected.SplitTorusStatement
import Langlands.GroupScheme.CentralIsogeny.Restriction
import Langlands.GroupScheme.CentralIsogeny.MaximalSplitTorusLiftProof

/-! # Maximal split tori of a simply connected cover -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A maximal split torus lifts through a supplied simply connected cover, with
the restriction a central isogeny of the actual commutative group schemes. -/
theorem simplyConnectedCoverSplitTorus :
    SimplyConnectedCoverSplitTorusStatement.{u} := by
  intro k _ G C π hπ S i hi
  obtain ⟨T, j, f, hj, hcomm, hflat, hsurj, hlfp⟩ :=
    centralIsogenyMaximalSplitTorusLift k C G
      hπ.isSimplyConnected.isSemisimple.isConnectedReductive
      hπ.isSemisimple.isConnectedReductive π hπ.isCentralIsogeny S i hi
  exact ⟨T, j, f, hj, hcomm,
    isCentralIsogeny_of_fppf_closed_subgroup_restriction
      hπ.isCentralIsogeny.isFinite hj.1.2 hi.1.2 f hcomm hflat hsurj hlfp⟩

end Langlands.GroupScheme
