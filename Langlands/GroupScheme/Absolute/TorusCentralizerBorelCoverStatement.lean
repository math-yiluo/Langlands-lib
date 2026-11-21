import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Lattice

/-! # Statement: points of a torus centralizer lie in Borel subgroups containing the torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Lemma 17.37. Let `G` be a smooth connected affine group over an algebraically closed
field `k` and let `s : S ⟶ G` be a closed torus. Every rational point `g ∈ G(k)` of the
centralizer `C_G(S)` is the image of a rational point of some Borel subgroup `i : B ⟶ G`
containing `S`; that is, `C_G(S)(k) ⊆ ⋃_{B ⊇ S} B(k)`. -/
def TorusCentralizerBorelCoverStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ G),
    IsTorus S.toGrp → IsClosedSubgroup s →
    ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      g ∈ (torusCentralizer s).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) →
      ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G)
        (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X),
        IsBorelSubgroup i ∧ SubgroupFunctor.range s ≤ SubgroupFunctor.range i ∧
          b ≫ i.hom.hom = g

end Langlands.GroupScheme
