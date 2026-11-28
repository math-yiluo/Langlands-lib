import Langlands.AlgebraicGeometry.HenselianBirationalSolution.SectionCharts

/-! # Right translation by a section

The map `x ↦ x c` on the open where `(x, c)` is defined is the pullback of the
right translation map of the law. In particular it is an open immersion.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} (m : BirationalGroupLaw g) (c : Sect g)

abbrev rightDom : Y.Opens := sectionPairRight c.1 c.2 ⁻¹ᵁ m.domain

abbrev rightMap : (rightDom m c).toScheme ⟶ Y := (sectionPairRight c.1 c.2 ∣_ m.domain) ≫ m.mul

instance : IsOpenImmersion (rightMap m c) :=
  MorphismProperty.of_isPullback (isPullback_sectionPairRight_restrict m c.1 c.2) inferInstance

@[reassoc]
theorem rightMap_comp : rightMap m c ≫ g = (rightDom m c).ι ≫ g := by
  rw [rightMap, Category.assoc, m.mul_comp, morphismRestrict_ι_assoc,
    pullback.lift_fst_assoc, Category.id_comp]

theorem rightDom_dense (hs : IsStrictDomain m) : FibreGenerizationDense g (rightDom m c : Set Y) :=
  FibreGenerizationDense.preimage_of_isPullback (isPullback_sectionPairRight c.1 c.2) hs.domain_snd

@[reassoc]
theorem sectionPairRight_comp {T : Scheme.{u}} (x : T ⟶ Y) :
    x ≫ sectionPairRight c.1 c.2 =
      pullback.lift x (x ≫ g ≫ c.1) (section_comp_g c.1 c.2 x).symm := by
  apply pullback.hom_ext <;> simp

theorem rightDom_defined {T : Scheme.{u}} (a : T ⟶ (rightDom m c).toScheme) :
    m.Defined (a ≫ (rightDom m c).ι) ((a ≫ (rightDom m c).ι) ≫ g ≫ c.1)
      (section_comp_g c.1 c.2 _).symm := by
  rintro _ ⟨t, rfl⟩
  rw [← sectionPairRight_comp c, Scheme.Hom.comp_apply]
  exact (a t).2

theorem rightMap_eq {T : Scheme.{u}} (a : T ⟶ (rightDom m c).toScheme) :
    a ≫ rightMap m c =
      m.mulPt (a ≫ (rightDom m c).ι) ((a ≫ (rightDom m c).ι) ≫ g ≫ c.1)
        (section_comp_g c.1 c.2 _).symm (rightDom_defined m c a) := by
  rw [rightMap, BirationalGroupLaw.mulPt, ← Category.assoc]
  congr 1
  apply m.liftDom_eq
  · rw [Category.assoc, morphismRestrict_ι_assoc, ← Category.assoc a, sectionPairRight_comp_assoc,
      pullback.lift_fst]
  · rw [Category.assoc, morphismRestrict_ι_assoc, ← Category.assoc a, sectionPairRight_comp_assoc,
      pullback.lift_snd]

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
