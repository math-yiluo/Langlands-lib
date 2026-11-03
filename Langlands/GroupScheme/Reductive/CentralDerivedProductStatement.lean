import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.Torus.Lattice

/-! # Central torus and derived subgroup generation for connected reductive groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every connected reductive field group is generated scheme-theoretically by an actual
central torus and its actual derived subgroup. -/
def ReductiveCentralDerivedProductStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      ∃ (Z : CommGroupScheme (Spec (CommRingCat.of k)))
        (D : GroupScheme (Spec (CommRingCat.of k)))
        (i : Z.toGrp ⟶ G) (d : D ⟶ G),
        IsAffineHom Z.toGrp.X.hom ∧ LocallyOfFiniteType Z.toGrp.X.hom ∧
        IsTorus Z.toGrp ∧ IsClosedSubgroup i ∧ IsCentral i ∧
        IsDerivedSubgroup d ∧ Epi (subgroupProductMap i d)

end Langlands.GroupScheme
