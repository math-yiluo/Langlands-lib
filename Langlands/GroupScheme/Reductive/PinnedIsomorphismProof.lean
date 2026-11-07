import Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction
import Langlands.GroupScheme.Reductive.SplitIsomorphismProof
import Langlands.GroupScheme.Reductive.PinnedRootScalingProof
import Langlands.GroupScheme.Reductive.PinnedRigidityProof

/-! # Unique actual pinned lifts of based root-datum isomorphisms -/

universe u

namespace Langlands.GroupScheme

/-- Every based equivalence of the full root data of supplied split pinnings
lifts to a unique actual pinned isomorphism with the prescribed lattice maps. -/
theorem pinnedIsomorphism : PinnedIsomorphismStatement.{u} :=
  PinnedIsomorphism.pinnedIsomorphismStatement_of_prerequisites
    ⟨splitCommonTorusIsomorphism, pinnedRootScaling, pinnedAutomorphismRigidity⟩

end Langlands.GroupScheme
