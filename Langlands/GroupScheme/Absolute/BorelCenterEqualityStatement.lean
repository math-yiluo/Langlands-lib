import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Rational.Characters

/-! # Statement: the centre of a Borel subgroup is the centre of the group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.45. Let `i : B ⟶ G` be a Borel subgroup, in the geometric sense, of
a smooth connected affine group over a field `k`. On every test scheme, the points of the
centre of `G` are exactly the images under `i` of the points of the centre of `B`. -/
def BorelCenterEqualityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsGeometricBorelSubgroup i →
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ∈ (center G).carrier T ↔
          ∃ y : T ⟶ B.X, y ∈ (center B).carrier T ∧ y ≫ i.hom.hom = x

end Langlands.GroupScheme
