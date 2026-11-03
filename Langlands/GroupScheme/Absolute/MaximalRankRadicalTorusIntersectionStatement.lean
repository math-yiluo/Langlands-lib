import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Radical intersections in connected subgroups of maximal rank -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, intersecting a specified ambient maximal
torus with the solvable radical of a smooth connected subgroup of maximal rank
gives an actual maximal torus of that radical on every test scheme. -/
def MaximalRankRadicalTorusIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
      IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
        IsMaximalTorus t → ∀ (f : T.toGrp ⟶ H), f ≫ j = t →
        ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ H),
          IsSolvableRadical r →
          ∃ (S : CommGroupScheme (Spec (CommRingCat.of k)))
            (sT : S.toGrp ⟶ T.toGrp) (sR : S.toGrp ⟶ R),
            IsClosedSubgroup sT ∧ IsMaximalTorus sR ∧
            sT ≫ f = sR ≫ r ∧
            SubgroupFunctor.range (sT ≫ f) =
              SubgroupFunctor.range f ⊓ SubgroupFunctor.range r

end Langlands.GroupScheme
