import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.SubgroupFunctor

/-! # Minimal rational parabolic subgroups and their functors of points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A subgroup functor is parabolic if it is the all-test range of an actual parabolic
subgroup over the ground field. -/
def IsParabolicFunctor (F : SubgroupFunctor G) : Prop :=
  ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
    IsParabolicSubgroup j ∧ SubgroupFunctor.range j = F

/-- A rational parabolic subgroup functor is minimal among rational parabolic subgroup
functors, with inclusion tested on every scheme over the ground field. -/
def IsMinimalParabolicFunctor (F : SubgroupFunctor G) : Prop :=
  IsParabolicFunctor F ∧
    ∀ F' : SubgroupFunctor G, IsParabolicFunctor F' → F' ≤ F → F' = F

/-- An actual parabolic subgroup is minimal among the parabolic subgroups defined over
the ground field. Its minimality concerns the all-test range, rather than just rational points. -/
def IsMinimalParabolicSubgroup {P : GroupScheme (Spec (CommRingCat.of k))}
    (j : P ⟶ G) : Prop :=
  IsParabolicSubgroup j ∧
    ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (j' : Q ⟶ G),
      IsParabolicSubgroup j' → SubgroupFunctor.range j' ≤ SubgroupFunctor.range j →
        SubgroupFunctor.range j' = SubgroupFunctor.range j

theorem IsMinimalParabolicSubgroup.isParabolicSubgroup
    {P : GroupScheme (Spec (CommRingCat.of k))} {j : P ⟶ G}
    (hj : IsMinimalParabolicSubgroup j) : IsParabolicSubgroup j :=
  hj.1

theorem IsMinimalParabolicFunctor.isParabolicFunctor
    {F : SubgroupFunctor G} (hF : IsMinimalParabolicFunctor F) : IsParabolicFunctor F :=
  hF.1

theorem IsMinimalParabolicSubgroup.isMinimalParabolicFunctor
    {P : GroupScheme (Spec (CommRingCat.of k))} {j : P ⟶ G}
    (hj : IsMinimalParabolicSubgroup j) :
    IsMinimalParabolicFunctor (SubgroupFunctor.range j) := by
  refine ⟨⟨P, j, hj.1, rfl⟩, ?_⟩
  rintro F' ⟨Q, j', hj', rfl⟩ hle
  exact hj.2 Q j' hj' hle

/-- A minimal parabolic functor has a representative that is an actual minimal parabolic
subgroup. This is an unpacking of the definitions, not an existence theorem for parabolics. -/
theorem isMinimalParabolicFunctor_iff_exists {F : SubgroupFunctor G} :
    IsMinimalParabolicFunctor F ↔
      ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
        IsMinimalParabolicSubgroup j ∧ SubgroupFunctor.range j = F := by
  constructor
  · rintro ⟨⟨P, j, hj, rfl⟩, hmin⟩
    refine ⟨P, j, ⟨hj, ?_⟩, rfl⟩
    intro Q j' hj' hle
    exact hmin (SubgroupFunctor.range j') ⟨Q, j', hj', rfl⟩ hle
  · rintro ⟨P, j, hj, rfl⟩
    exact hj.isMinimalParabolicFunctor

/-- Two minimal parabolic functors related by inclusion are equal. -/
theorem IsMinimalParabolicFunctor.eq_of_le
    {F F' : SubgroupFunctor G} (hF : IsMinimalParabolicFunctor F)
    (hF' : IsMinimalParabolicFunctor F') (hle : F' ≤ F) : F' = F :=
  hF.2 F' hF'.1 hle

end Langlands.GroupScheme
