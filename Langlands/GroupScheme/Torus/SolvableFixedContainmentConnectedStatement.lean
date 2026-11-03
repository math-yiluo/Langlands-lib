import Langlands.GroupScheme.Rational.WeightSemigroup

/-! # Connected invariant subgroups containing the fixed subgroup -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Torus

/-- A smooth invariant closed subgroup of a smooth connected solvable affine
group is connected if it contains the fixed subgroup of a split-torus action. -/
def SolvableFixedContainmentConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))),
    Smooth H.X.hom → IsAffineHom H.X.hom → ConnectedSpace H.X.left →
    RelativeRoot.IsSolvableScheme H →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))),
      IsSplitTorus S.toGrp →
      ∀ (c : AutomorphicAction S.toGrp H) (F : SubgroupFunctor H),
        c.IsStable F → c.fixedSubgroup ≤ F →
        ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (q : C ⟶ H),
          F.IsRepresentedBy q → IsClosedSubgroup q → Smooth C.X.hom →
          ConnectedSpace C.X.left

end Langlands.GroupScheme.Torus
