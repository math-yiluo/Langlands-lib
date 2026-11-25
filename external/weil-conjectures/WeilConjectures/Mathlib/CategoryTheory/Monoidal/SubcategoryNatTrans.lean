/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Monoidal natural transformations between restrictions to full monoidal subcategories

Let `P`, `Q`, `R` be monoidal properties of objects of monoidal categories `C`, `D`, `E`, and
`F : C ⥤ D`, `G : D ⥤ E`, `H : C ⥤ E` strong monoidal functors preserving them. A monoidal
natural isomorphism `e : F ⋙ G ≅ H` induces, by full faithfulness of the inclusion `R.ι`, an
isomorphism between the composite of the restrictions of `F` and `G` and the restriction of `H`
(`Functor.fullyFaithfulCancelRight`). This isomorphism is monoidal, for the monoidal structures
`ObjectProperty.monoidalLift` of the restrictions
(`CategoryTheory.ObjectProperty.isMonoidal_fullyFaithfulCancelRight_hom`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open MonoidalCategory Functor.LaxMonoidal

/-- The preimage of a morphism under the inclusion of a full subcategory. -/
@[simp]
lemma ι_preimage_hom {C : Type*} [Category* C] {P : ObjectProperty C} {X Y : P.FullSubcategory}
    (f : X.obj ⟶ Y.obj) : (P.ι.preimage f).hom = f :=
  P.ι.map_preimage f

section Lift

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  (F : C ⥤ D) [F.Monoidal] (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- The unit comparison of the restriction of a strong monoidal functor `F` to full monoidal
subcategories is the unit comparison of `F`. -/
@[simp]
lemma monoidalLift_ε_hom : (ε (Q.lift (P.ι ⋙ F) hF)).hom = ε F :=
  rfl

/-- The tensor comparison of the restriction of a strong monoidal functor `F` to full monoidal
subcategories is the tensor comparison of `F`. -/
@[simp]
lemma monoidalLift_μ_hom (X Y : P.FullSubcategory) :
    (μ (Q.lift (P.ι ⋙ F) hF) X Y).hom = μ F X.obj Y.obj :=
  rfl

end Lift

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  {R : ObjectProperty E} [R.IsMonoidal]
  {F : C ⥤ D} [F.Monoidal] {G : D ⥤ E} [G.Monoidal] {H : C ⥤ E} [H.Monoidal]
  (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
  (hG : ∀ X : Q.FullSubcategory, R (G.obj X.obj))
  (hH : ∀ X : P.FullSubcategory, R (H.obj X.obj))

/-- A monoidal natural isomorphism `e : F ⋙ G ≅ H` induces a monoidal natural isomorphism
between the composite of the restrictions of `F` and `G` to full monoidal subcategories and the
restriction of `H`. -/
lemma isMonoidal_fullyFaithfulCancelRight_hom (e : F ⋙ G ≅ H) [NatTrans.IsMonoidal e.hom] :
    NatTrans.IsMonoidal (Functor.fullyFaithfulCancelRight R.ι
      ((Iso.refl (P.ι ⋙ (F ⋙ G)) :
          (Q.lift (P.ι ⋙ F) hF ⋙ R.lift (Q.ι ⋙ G) hG) ⋙ R.ι ≅ P.ι ⋙ (F ⋙ G)) ≪≫
        Functor.isoWhiskerLeft P.ι e) :
      Q.lift (P.ι ⋙ F) hF ⋙ R.lift (Q.ι ⋙ G) hG ≅ R.lift (P.ι ⋙ H) hH).hom where
  unit := hom_ext _ (by
    have h := NatTrans.IsMonoidal.unit (τ := e.hom)
    simp only [Functor.LaxMonoidal.comp_ε] at h
    simpa using h)
  tensor X Y := hom_ext _ (by
    have h := NatTrans.IsMonoidal.tensor (τ := e.hom) X.obj Y.obj
    simp only [Functor.LaxMonoidal.comp_μ] at h
    simpa using h)

end CategoryTheory.ObjectProperty
