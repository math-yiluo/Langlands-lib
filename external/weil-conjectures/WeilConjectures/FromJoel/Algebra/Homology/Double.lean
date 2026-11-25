/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.Additive

/-!
# Functoriality of homological complexes lying in two degrees

Supplement to `Mathlib.Algebra.Homology.Double`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject Opposite

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D]

section

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

set_option backward.defeqAttrib.useBackward true in
/-- The differential `(double f hi₀₁).d i₀ i₁` identifies to `f`, as an
isomorphism in the category of arrows. -/
@[simps!]
noncomputable def arrowIsoDoubleD (hi₀₁' : i₀ ≠ i₁) :
    Arrow.mk ((double f hi₀₁).d i₀ i₁) ≅ Arrow.mk f :=
  Arrow.isoMk (doubleXIso₀ f hi₀₁) (doubleXIso₁ f hi₀₁ hi₀₁') (by simp [double_d _ _ hi₀₁'])

section

variable (hi₀₁' : i₀ ≠ i₁) (F : C ⥤ D) [F.PreservesZeroMorphisms]

open Classical in
/-- The degreewise isomorphism between the image by `F.mapHomologicalComplex _`
of `double f hi₀₁` and `double (F.map f) hi₀₁`. -/
noncomputable def mapHomologicalComplexObjDoubleXIso (n : ι) :
    ((F.mapHomologicalComplex _).obj (double f hi₀₁)).X n ≅
      (double (F.map f) hi₀₁).X n :=
  if h₀ : n = i₀ then
      eqToIso (by subst h₀; rfl) ≪≫ F.mapIso (doubleXIso₀ f hi₀₁) ≪≫
        (doubleXIso₀ (F.map f) hi₀₁).symm ≪≫ eqToIso (by subst h₀; rfl)
    else if h₁ : n = i₁ then
      eqToIso (by subst h₁; rfl) ≪≫ F.mapIso (doubleXIso₁ f hi₀₁ hi₀₁') ≪≫
        (doubleXIso₁ (F.map f) hi₀₁ hi₀₁').symm ≪≫ eqToIso (by subst h₁; rfl)
      else IsZero.iso (F.map_isZero (isZero_double_X _ _ _ h₀ h₁))
        (isZero_double_X _ _ _ h₀ h₁)

set_option backward.defeqAttrib.useBackward true in
/-- The image by `F.mapHomologicalComplex _` of `double f hi₀₁` identifies
to `double (F.map f) hi₀₁`. -/
@[simps!]
noncomputable def mapHomologicalComplexObjDoubleIso :
    (F.mapHomologicalComplex _).obj (double f hi₀₁) ≅ double (F.map f) hi₀₁ :=
  Hom.isoOfComponents (mapHomologicalComplexObjDoubleXIso f hi₀₁ hi₀₁' F) (fun i j hij ↦ by
    dsimp
    by_cases h₀ : i = i₀
    · by_cases h₁ : j = i₁
      · subst h₀ h₁
        simp [double_d _ _ hi₀₁', mapHomologicalComplexObjDoubleXIso, dite_eq_right hi₀₁'.symm]
      · simp [double_d_eq_zero₁ _ _ _ _ h₁]
    · simp [double_d_eq_zero₀ _ _ _ _ h₀])

end

end

section

variable (C) {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁) (hi₀₁' : i₀ ≠ i₁)

/-- The functor `Arrow C ⥤ HomologicalComplex C c` which sends `f : X₀ ⟶ X₁`
to the complex consisting of `f` in degrees `i₀` and `i₁`, and zero elsewhere. -/
@[simps -isSimp obj map]
noncomputable def doubleFunctor : Arrow C ⥤ HomologicalComplex C c where
  obj f := double f.hom hi₀₁
  map {f f'} φ :=
    mkHomFromDouble _ hi₀₁' (φ.left ≫ (doubleXIso₀ f'.hom hi₀₁).inv)
      (φ.right ≫ (doubleXIso₁ f'.hom hi₀₁ hi₀₁').inv) (by simp [double_d _ hi₀₁ hi₀₁'])
        (fun _ _ ↦ by rw [double_d_eq_zero₀ _ _ _ _ hi₀₁'.symm, comp_zero])

attribute [simp] doubleFunctor_obj
attribute [local simp] doubleFunctor_map

variable {C} (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.defeqAttrib.useBackward true in
/-- The functor `doubleFunctor C hi₀₁ hi₀₁' : Arrow C ⥤ HomologicalComplex C c`
commutes with the functors induced by `F : C ⥤ D`. -/
@[simps!]
noncomputable def doubleFunctorCompMapHomologicalComplex :
    doubleFunctor C hi₀₁ hi₀₁' ⋙ F.mapHomologicalComplex c ≅
      F.mapArrow ⋙ doubleFunctor D hi₀₁ hi₀₁' :=
  NatIso.ofComponents (fun f ↦ mapHomologicalComplexObjDoubleIso f.hom hi₀₁ hi₀₁' F) (fun φ ↦ by
      dsimp
      apply to_double_hom_ext
      · simp [mapHomologicalComplexObjDoubleXIso]
      · simp [mapHomologicalComplexObjDoubleXIso, dite_eq_right hi₀₁'.symm])

end

end HomologicalComplex
