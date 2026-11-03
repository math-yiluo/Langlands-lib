import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope

/-! # The least closed subgroup containing every ground-field torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G H K : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual closed subgroup containing all ground-field tori, least for
containment of images on every relative test scheme. -/
structure IsTorusGeneratedSubgroup (i : H ⟶ G) : Prop where
  isClosedSubgroup : IsClosedSubgroup i
  containsTori : (SubgroupFunctor.range i).ContainsTori
  least : ∀ (K : GroupScheme (Spec (CommRingCat.of k))) (j : K ⟶ G),
    IsClosedSubgroup j → (SubgroupFunctor.range j).ContainsTori →
      SubgroupFunctor.range i ≤ SubgroupFunctor.range j

namespace IsTorusGeneratedSubgroup

variable {i : H ⟶ G} (hi : IsTorusGeneratedSubgroup i)

include hi

/-- The least-image predicate has exactly the already defined closed envelope. -/
theorem range_eq_closedTorusEnvelope :
    SubgroupFunctor.range i = closedTorusEnvelope G := by
  apply le_antisymm
  · intro U x hx K j hj ht
    exact hi.least K j hj ht U hx
  · exact closedTorusEnvelope_le i hi.isClosedSubgroup hi.containsTori

/-- The least-image inclusion represents the fixed closed torus envelope. -/
theorem represents : (closedTorusEnvelope G).IsRepresentedBy i := by
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  exact ⟨Over.mono_of_mono_left _, hi.range_eq_closedTorusEnvelope⟩

/-- Package a least-image inclusion as representative data for the fixed envelope. -/
def toEnvelope : TorusGeneratedEnvelope G where
  group := H
  inclusion := i
  closed := hi.isClosedSubgroup
  represents := hi.represents

/-- Any two least-image inclusions have the same image on every test scheme. -/
theorem range_eq {j : K ⟶ G} (hj : IsTorusGeneratedSubgroup j) :
    SubgroupFunctor.range i = SubgroupFunctor.range j :=
  hi.range_eq_closedTorusEnvelope.trans hj.range_eq_closedTorusEnvelope.symm

/-- Any two least-image inclusions are isomorphic over the ambient group. -/
def iso {j : K ⟶ G} (hj : IsTorusGeneratedSubgroup j) : H ≅ K :=
  hi.toEnvelope.iso hj.toEnvelope

theorem iso_hom_comp {j : K ⟶ G} (hj : IsTorusGeneratedSubgroup j) :
    (hi.iso hj).hom ≫ j = i :=
  hi.toEnvelope.iso_hom_comp hj.toEnvelope

end IsTorusGeneratedSubgroup

/-- The least-image predicate is equivalent to closed representation of the
existing envelope; it introduces no alternative generated-subgroup model. -/
theorem isTorusGeneratedSubgroup_iff (i : H ⟶ G) :
    IsTorusGeneratedSubgroup i ↔
      IsClosedSubgroup i ∧ (closedTorusEnvelope G).IsRepresentedBy i := by
  constructor
  · intro hi
    exact ⟨hi.isClosedSubgroup, hi.represents⟩
  · rintro ⟨hi, hr⟩
    refine ⟨hi, ?_, ?_⟩
    · rw [hr.2]
      exact closedTorusEnvelope_containsTori G
    · intro K j hj ht
      rw [hr.2]
      exact closedTorusEnvelope_le j hj ht

/-- Every supplied envelope representative satisfies the least-image predicate. -/
theorem TorusGeneratedEnvelope.isTorusGeneratedSubgroup (D : TorusGeneratedEnvelope G) :
    IsTorusGeneratedSubgroup D.inclusion :=
  (isTorusGeneratedSubgroup_iff D.inclusion).mpr ⟨D.closed, D.represents⟩

end Langlands.GroupScheme
