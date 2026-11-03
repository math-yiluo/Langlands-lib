import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: smoothness of the centralizer of a torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Smoothness of torus centralizers** (Milne, Corollary 13.10, for a torus). Let `G` be a
smooth affine group scheme over a field `k` and `i : T ⟶ G` a closed torus. Every closed
subgroup `j : C ⟶ G` representing the all-test centralizer of `i` is smooth over `k`. -/
def TorusCentralizerSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsTorus T.toGrp → IsClosedSubgroup i →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (j : C ⟶ G),
      (torusCentralizer i).IsRepresentedBy j → IsClosedSubgroup j → Smooth C.X.hom

end Langlands.GroupScheme
