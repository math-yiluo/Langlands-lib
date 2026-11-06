import Langlands.GroupScheme.Reductive.Pinning

/-! # Statement: rigidity of actual pinned split reductive groups -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An automorphism of an actual pinned split connected reductive field group
that is the identity on the pinned torus and whose actual differential fixes
every chosen simple-root vector is the identity. -/
def PinnedAutomorphismRigidityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (p : SplitPinning G) (σ : G ≅ G),
    p.inclusion ≫ σ.hom = p.inclusion →
    (∀ a : p.base.support,
      Lie.targetMapLinear σ.hom (CommRingCat.of k) (p.pinning.rootVector a) =
        p.pinning.rootVector a) →
    σ = Iso.refl G

end Langlands.GroupScheme
