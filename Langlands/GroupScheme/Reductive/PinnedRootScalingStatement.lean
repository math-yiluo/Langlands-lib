import Langlands.GroupScheme.Reductive.Pinning

/-! # Statement: scaling the simple-root vectors of an actual pinning -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For every family of units indexed by the simple roots of an actual pinned
split connected reductive field group, some automorphism is the identity on
the pinned torus and its actual differential multiplies each chosen
simple-root vector by the corresponding unit. -/
def PinnedRootScalingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (p : SplitPinning G) (c : p.base.support → kˣ),
    ∃ σ : G ≅ G, p.inclusion ≫ σ.hom = p.inclusion ∧
      ∀ a : p.base.support,
        Lie.targetMapLinear σ.hom (CommRingCat.of k) (p.pinning.rootVector a) =
          (c a : k) • p.pinning.rootVector a

end Langlands.GroupScheme
