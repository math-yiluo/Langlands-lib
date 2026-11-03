import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # Actual parabolic subgroup functors and identity-test comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual parabolic subgroup functors, ordered by inclusion on every test scheme. -/
abbrev ParabolicFunctor (G : GroupScheme (Spec (CommRingCat.of k))) :=
  {F : SubgroupFunctor G // IsParabolicFunctor F}

/-- Actual parabolic subgroup functors contained in a specified all-test subgroup functor. -/
abbrev ParabolicFunctorBelow (P : SubgroupFunctor G) :=
  {Q : SubgroupFunctor G // IsParabolicFunctor Q ∧ Q ≤ P}

/-- The existing existential predicate recognizes any closed representative,
independently of the chosen presentation. -/
theorem isParabolicFunctor_iff_of_isRepresentedBy {F : SubgroupFunctor G} {j : H ⟶ G}
    (hj : IsClosedSubgroup j) (hrep : F.IsRepresentedBy j) :
    IsParabolicFunctor F ↔ IsParabolicSubgroup j := by
  constructor
  · rintro ⟨P, i, hi, hrange⟩
    exact hi.of_range_eq hj (hrange.trans hrep.2.symm)
  · intro h
    exact ⟨H, j, h, hrep.2⟩

/-- The all-test range of a closed subgroup is parabolic exactly when its
embedding is an actual parabolic subgroup. -/
theorem isParabolicFunctor_range_iff {j : H ⟶ G} (hj : IsClosedSubgroup j) :
    IsParabolicFunctor (SubgroupFunctor.range j) ↔ IsParabolicSubgroup j := by
  have : IsClosedImmersion j.hom.hom.left := hj
  exact isParabolicFunctor_iff_of_isRepresentedBy hj ⟨Over.mono_of_mono_left _, rfl⟩

namespace SubgroupFunctor

/-- The subgroup of rational points is evaluation at exactly the identity test scheme. -/
abbrev rationalPointSubgroup (F : SubgroupFunctor G) : Subgroup (RationalPoint k G.X) :=
  F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))

@[simp] theorem rationalPointSubgroup_inf (F F' : SubgroupFunctor G) :
    (F ⊓ F').rationalPointSubgroup = F.rationalPointSubgroup ⊓ F'.rationalPointSubgroup :=
  rfl

theorem mem_map_rationalPointSubgroup (j : H ⟶ G) (F : SubgroupFunctor H)
    (x : RationalPoint k G.X) :
    x ∈ (F.map j).rationalPointSubgroup ↔
      ∃ y ∈ F.rationalPointSubgroup, y ≫ j.hom.hom = x :=
  Iff.rfl

theorem mem_comap_rationalPointSubgroup (j : H ⟶ G) (F : SubgroupFunctor G)
    (x : RationalPoint k H.X) :
    x ∈ (F.comap j).rationalPointSubgroup ↔
      x ≫ j.hom.hom ∈ F.rationalPointSubgroup :=
  Iff.rfl

/-- Mapping the inverse image back into the ambient rational point group gives
the actual intersection with the represented subgroup. -/
theorem map_comap_rationalPointSubgroup (j : H ⟶ G) (F : SubgroupFunctor G) :
    ((F.comap j).map j).rationalPointSubgroup =
      (range j).rationalPointSubgroup ⊓ F.rationalPointSubgroup := by
  rw [map_comap, rationalPointSubgroup_inf]

namespace IsRepresentedBy

/-- The existing represented-points equivalence at the identity test scheme.
This is an algebraic group equivalence; no topology is chosen here. -/
def rationalPointsEquiv {F : SubgroupFunctor G} {j : H ⟶ G}
    (hrep : F.IsRepresentedBy j) :
    RationalPoint k H.X ≃* F.rationalPointSubgroup :=
  hrep.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of k))))

@[simp] theorem rationalPointsEquiv_apply_coe {F : SubgroupFunctor G} {j : H ⟶ G}
    (hrep : F.IsRepresentedBy j) (x : RationalPoint k H.X) :
    (hrep.rationalPointsEquiv x : RationalPoint k G.X) = x ≫ j.hom.hom :=
  rfl

theorem rationalPointsEquiv_symm_comp {F : SubgroupFunctor G} {j : H ⟶ G}
    (hrep : F.IsRepresentedBy j) (x : F.rationalPointSubgroup) :
    hrep.rationalPointsEquiv.symm x ≫ j.hom.hom = x :=
  hrep.pointsEquiv_symm_comp x

end IsRepresentedBy

end SubgroupFunctor

end Langlands.GroupScheme
