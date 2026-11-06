import Langlands.GroupScheme.RepresentabilityTransfer
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The closed subgroup fixed by one group-scheme endomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}} {G H : GroupScheme B}

/-- The points fixed by a single endomorphism, on every test scheme. -/
def endomorphismFixedSubgroup (f : G ⟶ G) : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | g ≫ f.hom.hom = g}
      one_mem' := MonObj.one_comp _
      mul_mem' := fun {g h} hg hh => by
        change g ≫ f.hom.hom = g at hg
        change h ≫ f.hom.hom = h at hh
        change (g * h) ≫ f.hom.hom = g * h
        rw [MonObj.mul_comp, hg, hh]
      inv_mem' := fun {g} hg => by
        change g ≫ f.hom.hom = g at hg
        change g⁻¹ ≫ f.hom.hom = g⁻¹
        rw [GrpObj.inv_comp, hg] }
  comp_mem {T T'} a {g} hg := by
    change g ≫ f.hom.hom = g at hg
    change (a ≫ g) ≫ f.hom.hom = a ≫ g
    rw [Category.assoc, hg]

@[simp]
theorem mem_endomorphismFixedSubgroup (f : G ⟶ G) {T : Over B} (g : T ⟶ G.X) :
    g ∈ (endomorphismFixedSubgroup f).carrier T ↔ g ≫ f.hom.hom = g := Iff.rfl

/-- The fixed subgroup is represented by the scheme equalizer. -/
theorem mem_endomorphismFixedSubgroup_iff_factors (f : G ⟶ G)
    {T : Over B} (g : T ⟶ G.X) :
    g ∈ (endomorphismFixedSubgroup f).carrier T ↔
      ∃ y : T ⟶ equalizer f.hom.hom (𝟙 G.X),
        y ≫ equalizer.ι f.hom.hom (𝟙 G.X) = g := by
  rw [mem_endomorphismFixedSubgroup]
  constructor
  · intro hg
    exact ⟨equalizer.lift g (by simpa using hg), equalizer.lift_ι _ _⟩
  · rintro ⟨y, rfl⟩
    simpa only [Category.assoc, Category.comp_id] using
      congrArg (fun z => y ≫ z) (equalizer.condition f.hom.hom (𝟙 G.X))

/-- A separated group scheme has a closed subgroup representing all fixed points. -/
theorem endomorphismFixedSubgroup_isClosedRepresentable (f : G ⟶ G)
    [IsSeparated G.X.hom] : (endomorphismFixedSubgroup f).IsClosedRepresentable :=
  (endomorphismFixedSubgroup f).isClosedRepresentable_of_scheme
    (equalizer.ι f.hom.hom (𝟙 G.X))
    (fun _ g => mem_endomorphismFixedSubgroup_iff_factors f g)

/-- A group map lands in the fixed subgroup exactly when its composite is fixed. -/
theorem range_le_endomorphismFixedSubgroup_iff (f : G ⟶ G) (i : H ⟶ G) :
    SubgroupFunctor.range i ≤ endomorphismFixedSubgroup f ↔ i ≫ f = i := by
  constructor
  · intro hi
    apply hom_ext_points
    intro T x
    have hx := hi T (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
    simpa only [mem_endomorphismFixedSubgroup, Grp.comp_hom_hom, Category.assoc] using hx
  · intro hi T g hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    change (x ≫ i.hom.hom) ≫ f.hom.hom = x ≫ i.hom.hom
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun j : H ⟶ G => x ≫ j.hom.hom) hi

/-- Fixedness on every test scheme is equivalent to equality with the identity. -/
theorem endomorphismFixedSubgroup_eq_top_iff (f : G ⟶ G) :
    endomorphismFixedSubgroup f = ⊤ ↔ f = 𝟙 G := by
  constructor
  · intro hf
    apply hom_ext_points
    intro T g
    have hg : g ∈ (endomorphismFixedSubgroup f).carrier T := by
      rw [hf]
      trivial
    simpa using hg
  · rintro rfl
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro g
    simp

end Langlands.GroupScheme
