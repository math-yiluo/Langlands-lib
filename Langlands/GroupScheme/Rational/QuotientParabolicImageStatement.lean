import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Statement: quotient maps carry parabolic and Borel subgroups to parabolic and Borel subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, 17.69. Let `q : G ⟶ Q` be a quotient map (flat and surjective) of smooth connected
affine groups over an arbitrary field `k`, and let `i : H ⟶ G` be a subgroup. If `i` is parabolic
(resp. a geometric Borel subgroup), then so is the image `q(H)`. The image is encoded as a smooth
closed subgroup `j : H' ⟶ Q` with `i ≫ q = f ≫ j` for a homomorphism `f : H ⟶ H'` whose
underlying map is surjective. -/
def QuotientParabolicImageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : G ⟶ Q), Flat q.hom.hom.left → Surjective q.hom.hom.left →
    ∀ (H H' : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (j : H' ⟶ Q) (f : H ⟶ H'),
      IsClosedSubgroup j → Smooth H'.X.hom → Surjective f.hom.hom.left → i ≫ q = f ≫ j →
        (IsParabolicSubgroup i → IsParabolicSubgroup j) ∧
        (IsGeometricBorelSubgroup i → IsGeometricBorelSubgroup j)

end Langlands.GroupScheme
