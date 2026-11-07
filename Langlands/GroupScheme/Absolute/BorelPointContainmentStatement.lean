import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: every rational point lies in a Borel subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Every element lies in a Borel subgroup** (Milne, Corollary 17.34). Let `G` be a smooth
affine group scheme with connected underlying space over an algebraically closed field `k`.
Every point `g ∈ G(k)` is the image of a point of some Borel subgroup `i : B ⟶ G`. -/
def BorelPointContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G)
      (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X),
      IsBorelSubgroup i ∧ b ≫ i.hom.hom = g

end Langlands.GroupScheme
