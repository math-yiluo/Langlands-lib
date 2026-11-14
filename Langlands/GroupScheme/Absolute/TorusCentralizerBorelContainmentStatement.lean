import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # Statement: Borel subgroups through a maximal torus contain its centralizer -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 17.29. Let `j : T ⟶ G` be a maximal torus of a smooth
connected affine group over an algebraically closed field, and let `i : B ⟶ G` be
a Borel subgroup containing `T`. Every connected closed subgroup inside the
centralizer of `T` lies in `B`; equivalently `C_G(T)° ⊆ B`. -/
def TorusCentralizerBorelContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
    ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
      SubgroupFunctor.range j ≤ SubgroupFunctor.range i →
      ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        IsClosedSubgroup h → ConnectedSpace H.X.left →
          SubgroupFunctor.range h ≤ torusCentralizer j →
            SubgroupFunctor.range h ≤ SubgroupFunctor.range i

end Langlands.GroupScheme
