import Langlands.GroupScheme.Reductive.PinnedRootScalingStatement
import Langlands.GroupScheme.Reductive.RootScalingAutomorphism

/-! # Simple-root scaling for an actual split pinning -/

universe u

namespace Langlands.GroupScheme

/-- Every tuple of simple-root units is realized by an actual automorphism
fixing the supplied torus and scaling the supplied Lie root vectors. -/
theorem pinnedRootScaling : PinnedRootScalingStatement.{u} := by
  intro k _ G _ p c
  exact ⟨p.rootScalingIso c, p.rootScalingIso_inclusion c,
    p.rootScalingIso_rootVector c⟩

end Langlands.GroupScheme
