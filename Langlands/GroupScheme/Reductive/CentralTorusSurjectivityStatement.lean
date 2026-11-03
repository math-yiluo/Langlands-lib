import Langlands.GroupScheme.Reductive.CentralDerivedProductStatement

/-! # A central torus and the derived subgroup cover a connected reductive group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For every connected reductive field group and every actual inclusion of its derived
subgroup, some actual closed central torus multiplies with that derived subgroup onto all
points of the underlying scheme of the group. -/
def ReductiveCentralTorusSurjectivityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsConnectedReductive G → IsDerivedSubgroup d →
      ∃ (Z : CommGroupScheme (Spec (CommRingCat.of k))) (i : Z.toGrp ⟶ G),
        IsAffineHom Z.toGrp.X.hom ∧ LocallyOfFiniteType Z.toGrp.X.hom ∧
        IsTorus Z.toGrp ∧ IsClosedSubgroup i ∧ IsCentral i ∧
        Function.Surjective (subgroupProductMap i d).left

end Langlands.GroupScheme
