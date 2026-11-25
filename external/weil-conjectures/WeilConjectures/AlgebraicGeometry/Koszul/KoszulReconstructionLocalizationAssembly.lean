/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate

/-! # Reflection and unit equations under localization

## References

* Stacks Tag 099M
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory

/-- If `P.ι ⋙ L` is a localization, a natural transformation `η : F ⟶ G` of functors out of
`D` that is an isomorphism on the objects `L.obj X` is a natural isomorphism. -/
theorem AlgebraicGeometry.Scheme.localizationNatTransIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (L : C ⥤ D) (W : MorphismProperty C)
    [(P.ι ⋙ L).IsLocalization (W.inverseImage P.ι)]
    (F G : D ⥤ E) (η : F ⟶ G)
    (hη : ∀ X : P.FullSubcategory, IsIso (η.app (L.obj X.obj))) :
    ∃ e : F ≅ G, e.hom = η := by
  let S := P.ι ⋙ L
  let V := W.inverseImage P.ι
  let R := (Functor.whiskeringLeft P.FullSubcategory D E).obj S
  have : R.Full := Localization.full_whiskeringLeft S V E
  have : R.Faithful := Localization.faithful_whiskeringLeft S V E
  have (X : P.FullSubcategory) : IsIso ((R.map η).app X) := hη X
  have : IsIso (R.map η) := NatIso.isIso_of_isIso_app _
  have : IsIso η := isIso_of_fully_faithful R η
  exact ⟨asIso η, rfl⟩

/-- If `P.ι ⋙ L` is a localization, the unit equation `uF ≫ e.hom = uG` holds at every object
once it holds at the objects `L.obj X`. -/
theorem AlgebraicGeometry.Scheme.localizationUnitEq
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (L : C ⥤ D) (W : MorphismProperty C)
    [(P.ι ⋙ L).IsLocalization (W.inverseImage P.ι)]
    (F G H : D ⥤ E) (e : F ≅ G)
    (uF : H ⟶ F) (uG : H ⟶ G)
    (hu : ∀ X : P.FullSubcategory,
      uF.app (L.obj X.obj) ≫ e.hom.app (L.obj X.obj) =
        uG.app (L.obj X.obj)) :
    ∀ X : D, uF.app X ≫ e.hom.app X = uG.app X := by
  have h : uF ≫ e.hom = uG :=
    Localization.natTrans_ext (P.ι ⋙ L) (W.inverseImage P.ι) hu
  intro X
  exact congrArg (fun η ↦ η.app X) h
