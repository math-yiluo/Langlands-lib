/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives

/-!
# The right derived functor on the unbounded derived category

If `F : C ⥤ D` is an additive functor between abelian categories, where `C`
has K-injective resolutions, we define the right derived functor
`F.rightDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D` between the
corresponding unbounded derived categories.

This is the analogue on the full derived category of
`CategoryTheory.Functor.rightDerivedFunctorPlus`. Following the construction
there, we first upgrade the K-injective derivability structure
`CochainComplex.KInjectives.localizerMorphism` to a right derivability
structure `HomotopyCategory.KInjectives.localizerMorphism` at the level of
homotopy categories, where the source category is equipped with the class of
isomorphisms. As a consequence, any functor from
`HomotopyCategory C (ComplexShape.up ℤ)` has a (pointwise) right derived
functor with respect to quasi-isomorphisms, and the unit of such a derived
functor is an isomorphism on K-injective complexes.

In mathlib, this file would be
`Mathlib/Algebra/Homology/DerivedCategory/RightDerivedFunctor.lean`.

-/

@[expose] public section

open CategoryTheory Abelian Limits

variable {C H : Type*} [Category C] [Abelian C] [Category H]

namespace HomotopyCategory

namespace KInjectives

variable (C) in
/-- The localizer morphism that is given by the "inclusion functor"
`HomotopyCategory.KInjectives C ⥤ HomotopyCategory C (ComplexShape.up ℤ)`.
The target category is equipped with the class of quasi-isomorphisms while
the source category `HomotopyCategory.KInjectives C` is equipped with the
class of isomorphisms (which is exactly the same as quasi-isomorphisms). -/
abbrev localizerMorphism : LocalizerMorphism
    (MorphismProperty.isomorphisms (KInjectives C))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) where
  functor := ι
  map K L f (hf : IsIso f) := by
    rw [MorphismProperty.inverseImage_iff, mem_quasiIso_iff]
    intro n
    infer_instance

variable [HasKInjectiveResolutions C]

instance [HasDerivedCategory C] :
    ((localizerMorphism C).functor ⋙ DerivedCategory.Qh).IsLocalization
      (MorphismProperty.isomorphisms (KInjectives C)) :=
  inferInstanceAs ((Qh (C := C)).IsLocalization _)

instance : (localizerMorphism C).IsLocalizedEquivalence := by
  let this := HasDerivedCategory.standard C
  exact .of_isLocalization_of_isLocalization _ DerivedCategory.Qh

instance (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    IsConnected ((localizerMorphism C).RightResolution X) := by
  let this := HasDerivedCategory.standard C
  obtain ⟨K, rfl⟩ := quotient_obj_surjective X
  obtain ⟨L, _, i, _, _⟩ := HasKInjectiveResolutions.exists_isKInjective K
  have : Nonempty ((localizerMorphism C).RightResolution ((quotient _ _).obj K)) :=
    ⟨{ X₁ := .mk L
       w := (quotient _ _).map i
       hw := by
        simpa [quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
          using inferInstanceAs (QuasiIso i) }⟩
  refine zigzag_isConnected (fun R₁ R₂ => ?_)
  obtain ⟨X₁, w₁, hw₁, rfl⟩ := R₁.mk_surjective
  obtain ⟨X₂, w₂, hw₂, rfl⟩ := R₂.mk_surjective
  obtain ⟨L₁, _, rfl⟩ := X₁.mk_surjective
  obtain ⟨L₂, _, rfl⟩ := X₂.mk_surjective
  have := Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) w₁ hw₁
  obtain ⟨f, hf⟩ := (Qh (C := C)).map_surjective
    (inv (DerivedCategory.Qh.map w₁) ≫ DerivedCategory.Qh.map w₂)
  exact Zigzag.of_hom
    { f := f
      comm := (CochainComplex.IsKInjective.Qh_map_bijective _ L₂).injective (by
        rw [Functor.map_comp]
        change _ ≫ (Qh (C := C)).map f = _
        rw [hf, IsIso.hom_inv_id_assoc]) }

/-- Auxiliary localizer morphism for the proof that
`HomotopyCategory.KInjectives.localizerMorphism` has right resolutions of arrows:
the quotient functor `CochainComplex.KInjectives C ⥤ HomotopyCategory.KInjectives C`
sends quasi-isomorphisms to isomorphisms. -/
private abbrev toHomotopyCategoryLocalizerMorphism :
    LocalizerMorphism (CochainComplex.KInjectives.quasiIso C)
      (MorphismProperty.isomorphisms (KInjectives C)) where
  functor := CochainComplex.KInjectives.toHomotopyCategory
  map _ _ f hf :=
    (CochainComplex.KInjectives.isIso_toHomotopyCategory_map_iff f).2 (by
      simpa [CochainComplex.KInjectives.quasiIso, MorphismProperty.inverseImage_iff,
        HomologicalComplex.mem_quasiIso_iff] using hf)

/-- Auxiliary localizer morphism for the proof that
`HomotopyCategory.KInjectives.localizerMorphism` has right resolutions of arrows:
the quotient functor `CochainComplex C ℤ ⥤ HomotopyCategory C (ComplexShape.up ℤ)`
sends quasi-isomorphisms to quasi-isomorphisms. -/
private abbrev quotientLocalizerMorphism :
    LocalizerMorphism (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) where
  functor := quotient C (ComplexShape.up ℤ)
  map _ _ f hf := by simpa [quotient_map_mem_quasiIso_iff] using hf

instance : (localizerMorphism C).arrow.HasRightResolutions :=
  LocalizerMorphism.hasRightResolutions_arrow_of_essSurj_of_full
    (T := CochainComplex.KInjectives.localizerMorphism C)
    (L := toHomotopyCategoryLocalizerMorphism)
    (R := quotientLocalizerMorphism)
    (B := localizerMorphism C)
    (Iso.refl _)

instance : (localizerMorphism C).IsRightDerivabilityStructure := .mk' _

section

variable (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H)

omit [HasKInjectiveResolutions C] in
lemma localizerMorphism_derives : (localizerMorphism C).Derives F :=
  MorphismProperty.isInvertedBy_isomorphisms _

/-- Any functor from the unbounded homotopy category of an abelian category
with K-injective resolutions has a right derived functor with respect to
quasi-isomorphisms. -/
instance : F.HasPointwiseRightDerivedFunctor (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (localizerMorphism_derives F).hasPointwiseRightDerivedFunctor

variable [HasDerivedCategory C] (F' : DerivedCategory C ⥤ H)
  (α : F ⟶ DerivedCategory.Qh ⋙ F')
  [F'.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

instance (K : CochainComplex C ℤ) [K.IsKInjective] :
    IsIso (α.app ((quotient _ _).obj K)) :=
  (localizerMorphism_derives F).isIso_of_isRightDerivedFunctor α (mk K)

end

end KInjectives

end HomotopyCategory

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [HasKInjectiveResolutions C]

/-- The right derived functor `DerivedCategory C ⥤ DerivedCategory D`
when `F : C ⥤ D` is an additive functor between abelian categories and
`C` has K-injective resolutions. -/
noncomputable def rightDerivedFunctor :
    DerivedCategory C ⥤ DerivedCategory D :=
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

@[inherit_doc rightDerivedFunctor]
scoped notation "R(" F ")" => rightDerivedFunctor F

/-- The natural transformation that is part of the data of
the right derived functor `DerivedCategory C ⥤ DerivedCategory D`
when `F : C ⥤ D` is an additive functor between abelian categories and
`C` has K-injective resolutions. -/
noncomputable def rightDerivedFunctorUnit :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ F.rightDerivedFunctor :=
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

instance : F.rightDerivedFunctor.IsRightDerivedFunctor
      F.rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [rightDerivedFunctor, rightDerivedFunctorUnit]
  infer_instance

example (K : CochainComplex C ℤ) [K.IsKInjective] :
    IsIso (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)) := by
  infer_instance

open ZeroObject in
/-- The right derived functor sends zero objects to zero objects: the zero complex is
K-injective, so the derived functor is computed on it by the additive functor `F`. -/
lemma isZero_rightDerivedFunctor_obj {X : DerivedCategory C} (hX : IsZero X) :
    IsZero (F.rightDerivedFunctor.obj X) := by
  have : (0 : CochainComplex C ℤ).IsKInjective :=
    ⟨fun f _ ↦ ⟨Homotopy.ofEq ((isZero_zero _).eq_of_tgt _ _)⟩⟩
  have h₀ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_isZero
    (isZero_zero (CochainComplex C ℤ))
  have h₁ : IsZero (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C _).obj 0)) :=
    DerivedCategory.Qh.map_isZero h₀
  have h₂ := ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map_isZero
    h₀).of_iso (asIso (F.rightDerivedFunctorUnit.app _)).symm
  exact h₂.of_iso (F.rightDerivedFunctor.mapIso (hX.iso h₁))

end Functor

end CategoryTheory
