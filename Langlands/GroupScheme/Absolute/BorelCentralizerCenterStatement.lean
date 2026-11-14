import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Statement: the centralizer of a Borel subgroup is the centre -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.22. Let `i : B ⟶ G` be a Borel subgroup of a smooth
connected affine group over an algebraically closed field. Every point of the
centre of `B` maps into the centralizer of `B` in `G`, and that centralizer is the
centre of `G`, both as all-test subgroup functors. -/
def BorelCentralizerCenterStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
      (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ B.X), x ∈ (center B).carrier T →
          x ≫ i.hom.hom ∈ (SubgroupFunctor.range i).centralizer.carrier T) ∧
        (SubgroupFunctor.range i).centralizer = center G

end Langlands.GroupScheme
