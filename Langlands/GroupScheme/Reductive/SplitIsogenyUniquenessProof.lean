import Langlands.GroupScheme.Reductive.SplitIsogenyRigidityReduction
import Langlands.GroupScheme.Reductive.IsogenyTorusRigidityProof

/-! # Unpinned uniqueness of split reductive isogenies -/

universe u

namespace Langlands.GroupScheme

/-- Split reductive isogenies with the same pullback on every torus character
differ by the inner action of a unique point of the supplied adjoint torus. -/
theorem splitIsogenyUniqueness : SplitIsogenyUniquenessStatement.{u} :=
  splitIsogenyRigidityReduction reductiveIsogenyTorusRigidity

end Langlands.GroupScheme
