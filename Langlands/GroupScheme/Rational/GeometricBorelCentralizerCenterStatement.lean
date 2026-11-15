import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Statement: the centralizer of a Borel subgroup over an arbitrary field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, 17.70. Let `i : B ⟶ G` be a Borel subgroup, in the geometric sense, of a smooth
connected affine group over a field `k`. Then `Z(B) = C_G(B) = Z(G)`:
* on every test scheme, the points of the centralizer `C_G(B)` of `B` in `G` are exactly the
  images under `i` of the points of the centre of `B`;
* the centralizer `C_G(B)` equals the centre of `G`, as subgroup functors. -/
def GeometricBorelCentralizerCenterStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsGeometricBorelSubgroup i →
      (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ∈ (SubgroupFunctor.range i).centralizer.carrier T ↔
          ∃ y : T ⟶ B.X, y ∈ (center B).carrier T ∧ y ≫ i.hom.hom = x) ∧
        (SubgroupFunctor.range i).centralizer = center G

end Langlands.GroupScheme
