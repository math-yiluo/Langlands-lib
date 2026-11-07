import Langlands.GroupScheme.Reductive.SplitPinnedOppositeFactorPairs

/-! # Rigidity of automorphisms of actual pinned reductive groups -/

universe u

namespace Langlands.GroupScheme

/-- An automorphism fixing the actual pinned torus and the simple pinning
vectors under its actual differential is the identity. -/
theorem pinnedAutomorphismRigidity : PinnedAutomorphismRigidityStatement.{u} := by
  exact pinnedAutomorphismRigidity_of_splitPinnedOppositeFactorPairs
    splitPinnedOppositeFactorPairs

end Langlands.GroupScheme
