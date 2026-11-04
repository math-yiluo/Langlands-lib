import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Normal solvable subgroups of reductive groups over algebraically closed fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, every smooth connected solvable normal
closed subgroup of a connected reductive group is a central torus. -/
def AlgClosedReductiveNormalSolvableTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsPseudoReductive G →
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
      IsClosedSubgroup h → Smooth H.X.hom → ConnectedSpace H.X.left →
        IsSolvableGroupScheme H → (SubgroupFunctor.range h).IsNormal →
          IsTorus H ∧ IsCentral h

end Langlands.GroupScheme
