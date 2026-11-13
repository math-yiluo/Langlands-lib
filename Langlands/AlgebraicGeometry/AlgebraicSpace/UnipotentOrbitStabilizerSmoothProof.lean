import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitStabilizerSmoothReduction
import Langlands.GroupScheme.ReducedBaseSmoothProof
import Langlands.GroupScheme.Unipotent.CharZeroConnectedProof

/-!
# Stabilizers of unipotent actions with constant orbit dimension are smooth

The published reduction `unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected`
derives `UnipotentOrbitStabilizerSmoothStatement` from SGA 3, Exposé VI_B, Corollaire 4.4
over a reduced base with connected fibres (`ReducedBaseConnectedFibreSmoothStatement`) and
from Milne, Corollary 14.15 (`CharZeroUnipotentConnectedStatement`). Both inputs are proved
in the Library, so the target holds.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Stabilizers of unipotent actions with constant orbit dimension are smooth: over a field
of characteristic zero, the stabilizer scheme of an action of an affine unipotent group
locally of finite type on a reduced scheme locally of finite type, all of whose points have
orbit dimension `d`, is smooth over that scheme. -/
theorem unipotentOrbitStabilizerSmooth : UnipotentOrbitStabilizerSmoothStatement.{u} :=
  unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected
    GroupScheme.reducedBaseConnectedFibreSmooth GroupScheme.charZeroUnipotentConnected

end Langlands.AlgebraicGeometry.AlgebraicSpace
