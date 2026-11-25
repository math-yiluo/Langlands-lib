/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Localizing subcategories and the indexing universe

Source: the nonzero-support argument of
`lem-exc-coproduct-preservation-universe-extension`, applied to the definition of a
localizing subcategory in `definition-localizing-subcategory`
(blueprint: lem-sfb-localizing-subcategory-universe).
-/

@[expose] public section

set_option autoImplicit false

universe u v w w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The direct-sum clause of `IsLocalizingSubcategoryOfSize.{u}`, as closure under the colimits of
shape `Discrete I` for `I : Type u`. -/
theorem IsLocalizingSubcategoryOfSize.isClosedUnderColimitsOfShape_discrete
    {C : Type v} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {P : ObjectProperty C} (hP : IsLocalizingSubcategoryOfSize.{u} P) (I : Type u) :
    P.IsClosedUnderColimitsOfShape (Discrete I) := by
  have := hP.2.1
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨E, hE⟩
  exact hP.2.2 E inferInstance (fun i ↦ hE ⟨i⟩)

/-- Closure under the existing coproducts of a universe in which the category is locally small is
closure under all existing coproducts, whatever their index: the nonzero summands of an existing
coproduct form a small family (`ObjectProperty.isClosedUnderColimitsOfShape_discrete_of_small`).
The triangulated and replete conditions are unchanged. -/
theorem isLocalizingSubcategoryOfSize_of_locallySmall
    {C : Type v} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{u} C] (P : ObjectProperty C)
    (hP : IsLocalizingSubcategoryOfSize.{u} P) : IsLocalizingSubcategoryOfSize.{w₂} P := by
  have : P.IsClosedUnderIsomorphisms := hP.2.1
  refine ⟨hP.1, hP.2.1, ?_⟩
  intro I E hE hobj
  -- the `LocallySmall` instance is passed explicitly: the index of the shared lemma is read off it
  have : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    @ObjectProperty.isClosedUnderColimitsOfShape_discrete_of_small C _ _ ‹LocallySmall.{u} C› P _
      hP.isClosedUnderColimitsOfShape_discrete I
  let := hE
  exact P.prop_colimit E (fun j ↦ hobj j.as)

/-- Closure under the existing coproducts of a universe in which the category is locally small is
closure under all existing coproducts in the universe of the morphisms:
`IsLocalizingSubcategory`. -/
theorem isLocalizingSubcategory_of_locallySmall
    {C : Type v} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{u} C] (P : ObjectProperty C)
    (hP : IsLocalizingSubcategoryOfSize.{u} P) : IsLocalizingSubcategory P :=
  have h : IsLocalizingSubcategoryOfSize.{w} P :=
    @isLocalizingSubcategoryOfSize_of_locallySmall C _ _ _ _ _ _ ‹LocallySmall.{u} C› P hP
  ⟨h.1, h.2.1, fun F hF hobj ↦ h.2.2 F hF hobj⟩

end CategoryTheory
