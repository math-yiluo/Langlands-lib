import Langlands.GroupScheme.Reductive.ConnectedActionInnerReduction
import Langlands.AbelianScheme.FiberwiseIsogeny
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.Torus.IsomorphismLocus
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.Topology.Connected.Clopen

/-! # Clopen subgroups of groups with connected fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- An open and closed subgroup of a group with connected residue fibres is
the entire group, without smoothness or finiteness hypotheses. -/
theorem isIso_of_clopen_of_connectedFibers {S : Scheme.{u}}
    {G H : GroupScheme S} (j : G ⟶ H)
    [IsOpenImmersion j.hom.hom.left] [IsClosedImmersion j.hom.hom.left]
    (hH : ∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber H s).X.left) :
    IsIso j :=
  isIso_clopen_subgroup_of_connectedFibres j hH

/-- The actual isomorphism supplied by a clopen subgroup embedding when the
target has connected residue fibres. Its forward map is the original map. -/
def clopenConnectedFibersIso {S : Scheme.{u}}
    {G H : GroupScheme S} (j : G ⟶ H)
    [IsOpenImmersion j.hom.hom.left] [IsClosedImmersion j.hom.hom.left]
    (hH : ∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber H s).X.left) :
    G ≅ H :=
  clopenSubgroupIsoOfConnectedFibres j hH

end Langlands.GroupScheme
