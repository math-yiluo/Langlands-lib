/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# Single-object quotient comparisons and shifts

Source: Mathlib single functors and their canonical quotient comparisons.
(blueprint: lem-pc-single-quotient-inverse-shift).
-/

@[expose] public section

universe uB vB
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
private theorem map_lift_single_shift_inv
    {A D E : Type*} [Category A] [Category D] [Category E]
    [HasShift D ℤ] [HasShift E ℤ]
    (F : SingleFunctors A E ℤ) (J : D ⥤ E) [J.Full] [J.Faithful] [J.CommShift ℤ]
    (Φ : ℤ → A ⥤ D) (e : ∀ i, Φ i ⋙ J ≅ F.functor i)
    (k i j : ℤ) (h : k + i = j) (X : A) :
    J.map (((SingleFunctors.lift F J Φ e).shiftIso k i j h).inv.app X) =
    (e i).hom.app X ≫ (F.shiftIso k i j h).inv.app X ≫
      ((e j).inv.app X)⟦k⟧' ≫ (J.commShiftIso k).inv.app ((Φ j).obj X) := by
  simp [SingleFunctors.lift, SingleFunctors.lift.shiftIso,
    Functor.FullyFaithful.whiskeringRight, Functor.FullyFaithful.ofFullyFaithful]

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory B]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The single/quotient comparison intertwines inverse single shifts.

Source: Mathlib `SingleFunctors.lift`, `SingleFunctors.postcomp`, and
`DerivedCategory.singleFunctorsPostcompQIso`.
(blueprint: lem-pc-single-quotient-inverse-shift)

Proof: First apply the faithful inclusion to the comparison e_i. Unfolding
preimageIso and the quotient comparisons shows that its inverse is the identity.
After removing these identities, apply the faithful inclusion again. Expand
both lifted inverse single shifts and the ambient single functors as
postcomposition by Qh. Compute the inclusion image of Qh.commShiftIso using
Functor.CommShift.OfComp.map_iso_hom_app. The inclusion shift comparison and
its inverse cancel under Qh; the remaining composites agree. This holds also
at n = 0, where both sides are the inverse shift-zero comparison. -/
theorem single_quotient_inverse_shift (X : B) (n : ℕ) :
    let e (i : ℤ) : (DerivedCategory.Plus.singleFunctor B i).obj X ≅
        DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B i).obj X) :=
      DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.singleFunctorIsoCompQ B i).app X ≪≫
        (DerivedCategory.quotientCompQhIso B).symm.app _)
    let K₀ := (HomotopyCategory.Plus.singleFunctor B 0).obj X
    let h := ((HomotopyCategory.Plus.singleFunctors B).shiftIso
      (-(n : ℤ)) n 0 (by simp)).inv.app X
    (e n).inv ≫ ((DerivedCategory.Plus.singleFunctors B).shiftIso
      (-(n : ℤ)) n 0 (by simp)).inv.app X =
    DerivedCategory.Plus.Qh.map h ≫
      (DerivedCategory.Plus.Qh.commShiftIso (-(n : ℤ))).hom.app K₀ ≫
      ((e 0).inv)⟦-(n : ℤ)⟧' := by
  intro e K₀ h
  let E := DerivedCategory.singleFunctorsPostcompQhIso B
  have he (i : ℤ) : DerivedCategory.Plus.ι.map (e i).inv = (E.inv.hom i).app X := by
    simp only [e, Functor.preimageIso_inv, Functor.map_preimage, Iso.trans_inv]
    change (DerivedCategory.quotientCompQhIso B).hom.app
        ((CochainComplex.singleFunctor B i).obj X) ≫ 𝟙 _ =
      𝟙 _ ≫ (DerivedCategory.quotientCompQhIso B).hom.app
        ((CochainComplex.singleFunctor B i).obj X)
    rw [Category.comp_id, Category.id_comp]
  have hσD : DerivedCategory.Plus.ι.map
      (((DerivedCategory.Plus.singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).inv.app X) ≫
      (DerivedCategory.Plus.ι.commShiftIso (-(n : ℤ))).hom.app
        ((DerivedCategory.Plus.singleFunctor B 0).obj X) =
      ((DerivedCategory.singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).inv.app X := by
    simp only [DerivedCategory.Plus.singleFunctors, map_lift_single_shift_inv,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    simp only [ObjectProperty.ι_obj, comp_obj, ObjectProperty.lift_obj_obj, map_id,
      Category.id_comp, Category.assoc]
    erw [Iso.inv_hom_id_app, Category.comp_id]
  have hσH : (HomotopyCategory.Plus.ι B).map h ≫
      ((HomotopyCategory.Plus.ι B).commShiftIso (-(n : ℤ))).hom.app K₀ =
      ((HomotopyCategory.singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).inv.app X := by
    dsimp only [h]
    simp only [HomotopyCategory.Plus.singleFunctors, map_lift_single_shift_inv,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    simp only [ObjectProperty.ι_obj, comp_obj, ObjectProperty.lift_obj_obj, map_id,
      Category.id_comp, Category.assoc]
    erw [Iso.inv_hom_id_app, Category.comp_id]
  have hq := Functor.CommShift.OfComp.map_iso_hom_app
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (HomotopyCategory.Plus.ι B ⋙ DerivedCategory.Qh)
      (fun K ↦ (DerivedCategory.Plus.Qh.obj K).property)) (-(n : ℤ)) K₀
  simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.commShiftIso_comp_hom_app, Category.id_comp] at hq
  have hmap : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map h) ≫
      DerivedCategory.Plus.ι.map
        ((DerivedCategory.Plus.Qh.commShiftIso (-(n : ℤ))).hom.app K₀) ≫
      (DerivedCategory.Plus.ι.commShiftIso (-(n : ℤ))).hom.app
        (DerivedCategory.Plus.Qh.obj K₀) =
      (((HomotopyCategory.singleFunctors B).postcomp DerivedCategory.Qh).shiftIso
        (-(n : ℤ)) n 0 (by simp)).inv.app X := by
    erw [hq]
    simp only [Category.assoc, SingleFunctors.postcomp_shiftIso_inv_app]
    erw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
    change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι B).map h) ≫
      DerivedCategory.Qh.map
        (((HomotopyCategory.Plus.ι B).commShiftIso (-(n : ℤ))).hom.app K₀) ≫ _ = _
    erw [← Functor.map_comp_assoc, hσH]
    rfl
  have hc := congr_app (E.inv.comm (-(n : ℤ)) n 0 (by simp)) X
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hc
  have hc' : (E.inv.hom n).app X ≫
      ((DerivedCategory.singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).inv.app X =
      (((HomotopyCategory.singleFunctors B).postcomp DerivedCategory.Qh).shiftIso
        (-(n : ℤ)) n 0 (by simp)).inv.app X ≫ ((E.inv.hom 0).app X)⟦-(n : ℤ)⟧' := by
    rw [← cancel_epi
      ((((HomotopyCategory.singleFunctors B).postcomp DerivedCategory.Qh).shiftIso
        (-(n : ℤ)) n 0 (by simp)).hom.app X)]
    rw [← Category.assoc, hc]
    simp
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp]
  rw [← cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (-(n : ℤ))).hom.app
    ((DerivedCategory.Plus.singleFunctor B 0).obj X))]
  simp only [Category.assoc]
  rw [hσD, Functor.commShiftIso_hom_naturality]
  simp only [he]
  rw [reassoc_of% hmap]
  exact hc'

end CategoryTheory.Functor
