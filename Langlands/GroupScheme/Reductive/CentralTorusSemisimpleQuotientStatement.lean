import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.Lattice

/-! # A connected reductive group has a central torus with semisimple quotient -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every connected reductive field group has an actual closed central torus such that every
affine fppf quotient of the group by that torus is semisimple. -/
def ReductiveCentralTorusSemisimpleQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      ∃ (Z : CommGroupScheme (Spec (CommRingCat.of k))) (j : Z.toGrp ⟶ G),
        IsAffineHom Z.toGrp.X.hom ∧ LocallyOfFiniteType Z.toGrp.X.hom ∧
        IsTorus Z.toGrp ∧ IsClosedSubgroup j ∧ IsCentral j ∧
        ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q →
          IsAffineHom Q.X.hom → LocallyOfFiniteType Q.X.hom → IsSemisimple Q

end Langlands.GroupScheme
