import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # A rational Levi adapted to a maximal torus in a parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The intersection of a rational maximal torus with the geometric solvable
radical of a parabolic is a radical maximal torus and the largest central torus
of a rational Levi, represented by its whole-torus ambient centralizer. -/
def ParabolicRadicalTorusLeviStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
        IsMaximalTorus t → ∀ f : T.toGrp ⟶ P, f ≫ j = t →
          ∃ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P),
            IsGeometricSolvableRadical r ∧
            ∃ (S : CommGroupScheme (Spec (CommRingCat.of k)))
              (sT : S.toGrp ⟶ T.toGrp) (sR : S.toGrp ⟶ R),
              IsClosedSubgroup sT ∧ IsMaximalTorus sR ∧
              sT ≫ f = sR ≫ r ∧
              SubgroupFunctor.range (sT ≫ f) =
                SubgroupFunctor.range f ⊓ SubgroupFunctor.range r ∧
              ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P)
                (sL : S.toGrp ⟶ L),
                IsRationalLeviSubgroup l ∧
                (torusCentralizer (sT ≫ t)).IsRepresentedBy (l ≫ j) ∧
                sL ≫ l = sT ≫ f ∧ IsLargestCentralSubtorus sL

end Langlands.GroupScheme
