import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.SplitSolvable

/-! # Rational conjugation of split solvable subgroups into pseudo-parabolics -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- CGP Lemma C.2.2, with an actual rational conjugator and a factorization
of group-scheme homomorphisms over the original field. -/
def SplitSolvableIntoPseudoParabolicStatement : Prop :=
  ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : P ⟶ G), IsPseudoParabolicSubgroup i →
      ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
        IsClosedSubgroup j → IsSplitSolvableGroupScheme H →
          ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (f : H ⟶ P),
            f ≫ i = j ≫ (G.innerIso g).hom

end Langlands.GroupScheme
