import Langlands.GroupScheme.Rational.ParabolicTorusStatement

/-! # Split parts of maximal tori in minimal rational parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The maximal split part of any rational maximal torus contained in a minimal rational
parabolic is ambient maximal split, and its whole-torus centralizer lies in that parabolic
on every test scheme. -/
def MinimalParabolicTorusSplitPartStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsMinimalParabolicSubgroup j →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
        IsMaximalTorus t → ∀ f : T.toGrp ⟶ P, f ≫ j = t →
          ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ T.toGrp),
            IsMaximalSplitTorus a →
              IsMaximalSplitTorus (a ≫ t) ∧
                torusCentralizer (a ≫ t) ≤ SubgroupFunctor.range j

end Langlands.GroupScheme
