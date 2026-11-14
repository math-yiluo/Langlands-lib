import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: the conjugates of a Borel subgroup cover the group -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne, Theorem 17.33(b). Let `i : B ⟶ G` be a Borel subgroup of a smooth connected affine
group over an algebraically closed field `k`. The conjugation morphism
`G × B ⟶ G`, `(g, b) ↦ g i(b) g⁻¹`, is surjective on underlying spaces: the conjugates of `B`
cover `G`. -/
def BorelConjugateCoverStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
      Surjective (fst G.X B.X * (snd G.X B.X ≫ i.hom.hom) * (fst G.X B.X)⁻¹).left

end Langlands.GroupScheme
