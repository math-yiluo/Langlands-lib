import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Pseudo-parabolic descent under a supplied split-radical quotient

This is the structural descent target used in the first reduction of
CGP Lemma C.2.1. No quotient model is chosen and no proof is asserted.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every supplied fppf quotient by the split ground-field unipotent radical
admits a pseudo-parabolic subgroup with exactly the original full preimage. -/
def PseudoParabolicSplitRadicalQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
    ∀ (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
      IsSplitUnipotentRadical n →
      ∀ f : G ⟶ H,
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) f →
        ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
          IsPseudoParabolicSubgroup i →
          ∃ (K : GroupScheme (Spec (CommRingCat.of k))) (j : K ⟶ H),
            IsPseudoParabolicSubgroup j ∧
              SubgroupFunctor.range i = (SubgroupFunctor.range j).comap f

end Langlands.GroupScheme
