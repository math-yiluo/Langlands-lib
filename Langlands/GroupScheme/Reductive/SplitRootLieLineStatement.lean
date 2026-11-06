import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: root Lie spaces of split maximal tori are lines -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an arbitrary field, each root space of an actual split maximal torus
in a connected reductive group is a free module of rank one. -/
def SplitRootLieLineStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      ∀ χ ∈ roots i, Nonempty (k ≃ₗ[k] weightSpace i χ)

end Langlands.GroupScheme
