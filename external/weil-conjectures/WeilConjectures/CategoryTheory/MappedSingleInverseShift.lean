/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Single-object quotient comparisons and shifts

Source: Mathlib single functors and their canonical quotient comparisons.
(blueprint: lem-pc-mapped-single-inverse-shift).
-/

@[expose] public section

universe uB vB uC vC
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

private theorem singleFunctors_comm_inv
    {A D : Type*} [Category A] [Category D] [HasShift D ℤ]
    {F F' : SingleFunctors A D ℤ} (α : F ⟶ F')
    (k i j : ℤ) (h : k + i = j) (X : A) :
    (α.hom i).app X ≫ (F'.shiftIso k i j h).inv.app X =
      (F.shiftIso k i j h).inv.app X ≫ ((α.hom j).app X)⟦k⟧' := by
  apply (cancel_epi ((F.shiftIso k i j h).hom.app X)).1
  have hα := congr_app (α.comm k i j h) X
  simp only [NatTrans.comp_app, whiskerRight_app] at hα
  rw [← Category.assoc, hα]
  simp

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The mapped-single comparison intertwines inverse single shifts.

Source: Mathlib `HomologicalComplex.singleMapHomologicalComplex`,
`SingleFunctors.postcomp`, the quotient shift comparisons, and the upstream
`Functor.mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app`.
(blueprint: lem-pc-mapped-single-inverse-shift)

Proof: Apply the faithful inclusion into the unbounded derived category.
Expand mapHomotopyCategoryPlusSingleFunctorQhObjIso as Q applied to the
termwise mapped-single isomorphism. Expand each single shift as the image of
the complex single shift followed by the quotient shift comparison. The
termwise mapped-single isomorphism commutes with the single shift by the
upstream mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app. Precompose
with the image of the forward single shift and cancel its inverse to obtain
the inverse-shift equation. Its quotient therefore commutes as well. Naturality
and composition of the quotient commShiftIso combine the two quotient shift
comparisons on the right. Faithfulness lifts
the resulting equation back to the bounded-below category. No exactness of G
is needed, and n = 0 gives the shift-zero comparison on both sides. -/
theorem mapped_single_inverse_shift (G : B ⥤ C) [G.Additive] (X : B) (n : ℕ) :
    let K₀ := (HomotopyCategory.Plus.singleFunctor B 0).obj X
    let h := ((HomotopyCategory.Plus.singleFunctors B).shiftIso
      (-(n : ℤ)) n 0 (by simp)).inv.app X
    (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫
      ((DerivedCategory.Plus.singleFunctors C).shiftIso
        (-(n : ℤ)) n 0 (by simp)).inv.app (G.obj X) =
    DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map h) ≫
      DerivedCategory.Plus.Qh.map
        ((G.mapHomotopyCategoryPlus.commShiftIso (-(n : ℤ))).hom.app K₀) ≫
      (DerivedCategory.Plus.Qh.commShiftIso (-(n : ℤ))).hom.app
        (G.mapHomotopyCategoryPlus.obj K₀) ≫
      ((G.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 X).hom)⟦-(n : ℤ)⟧' := by
  intro K₀ h
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, mapHomotopyCategoryPlusSingleFunctorQhObjIso,
    Functor.preimageIso_hom, Functor.map_preimage]
  simp only [DerivedCategory.Plus.singleFunctors, map_lift_single_shift_inv,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, Functor.map_id, Category.id_comp]
  simp only [DerivedCategory.singleFunctors, SingleFunctors.postcomp_shiftIso_inv_app,
    Category.assoc]
  apply (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (-(n : ℤ))).hom.app
    ((DerivedCategory.Plus.singleFunctor C 0).obj (G.obj X)))).1
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  erw [DerivedCategory.Plus.ι.commShiftIso_hom_naturality]
  rw [Functor.map_preimage]
  have hq := Functor.CommShift.OfComp.map_iso_hom_app
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh)
      (fun K ↦ (DerivedCategory.Plus.Qh.obj K).property)) (-(n : ℤ))
      (G.mapHomotopyCategoryPlus.obj K₀)
  simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.commShiftIso_comp_hom_app, Category.id_comp] at hq
  erw [hq]
  erw [Functor.map_id, Category.id_comp]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  have hs := singleFunctors_comm_inv
    (DerivedCategory.singleFunctorsPostcompQhIso C).inv
    (-(n : ℤ)) n 0 (by simp) (G.obj X)
  simp only [SingleFunctors.postcomp_functor, comp_obj, DerivedCategory.singleFunctors,
    DerivedCategory.Q_obj_single_obj, DerivedCategory.singleFunctorsPostcompQhIso, Iso.trans_inv,
    Iso.symm_inv, SingleFunctors.comp_hom, NatTrans.comp_app,
    SingleFunctors.postcompPostcompIso_hom_hom_app, SingleFunctors.postcompIsoOfIso_inv_hom_app,
    SingleFunctors.postcomp_shiftIso_inv_app, CochainComplex.shiftFunctor_obj_X',
    NatIso.ofComponents_inv_app, Category.assoc, map_comp] at hs
  erw [Category.id_comp, Functor.map_id, Category.id_comp] at hs
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  erw [hs]
  erw [← DerivedCategory.quotientCompQhIso_hom_naturality]
  simp only [Functor.map_comp, ← Category.assoc]
  apply (cancel_mono (((DerivedCategory.quotientCompQhIso C).hom.app
    ((CochainComplex.singleFunctor C 0).obj (G.obj X)))⟦-(n : ℤ)⟧')).2
  simp only [Category.assoc]
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).app X).hom) ≫
    DerivedCategory.Qh.map
      (((HomotopyCategory.singleFunctors C).shiftIso (-(n : ℤ)) n 0 (by simp)).inv.app
        (G.obj X)) ≫ (DerivedCategory.Qh.commShiftIso (-(n : ℤ))).hom.app _ =
    DerivedCategory.Qh.map ((G.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.Plus.ι B).map h)) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C).map
      ((G.mapHomotopyCategoryPlus.commShiftIso (-(n : ℤ))).hom.app K₀)) ≫
    DerivedCategory.Qh.map (((HomotopyCategory.Plus.ι C).commShiftIso
      (-(n : ℤ))).hom.app (G.mapHomotopyCategoryPlus.obj K₀)) ≫
    (DerivedCategory.Qh.commShiftIso (-(n : ℤ))).hom.app _ ≫
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).app X).hom))⟦-(n : ℤ)⟧'
  have hg := Functor.CommShift.OfComp.map_iso_hom_app
    ((HomotopyCategory.plus C).liftCompιIso
      (HomotopyCategory.Plus.ι B ⋙ G.mapHomotopyCategory (.up ℤ))
      (fun K ↦ (G.mapHomotopyCategoryPlus.obj K).property)) (-(n : ℤ)) K₀
  simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.commShiftIso_comp_hom_app, Category.id_comp] at hg
  erw [hg]
  erw [Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  dsimp only [h]
  simp only [HomotopyCategory.Plus.singleFunctors, map_lift_single_shift_inv,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  erw [← DerivedCategory.Qh.commShiftIso_hom_naturality]
  simp only [← Functor.map_comp_assoc]
  apply (cancel_mono ((DerivedCategory.Qh.commShiftIso (-(n : ℤ))).hom.app
    (((HomotopyCategory.singleFunctors C).functor 0).obj (G.obj X)))).2
  apply DerivedCategory.Qh.congr_map
  simp only [HomotopyCategory.singleFunctors, SingleFunctors.postcomp_shiftIso_inv_app]
  have hf := NatTrans.shift_app_comm
    (G.mapHomotopyCategoryFactors (.up ℤ)).hom (-(n : ℤ))
    ((CochainComplex.singleFunctor B 0).obj X)
  simp only [Functor.commShiftIso_comp_hom_app, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift, NatIso.ofComponents_hom_app, Iso.refl_hom, Functor.comp_obj] at hf
  erw [Functor.map_id, Category.comp_id, Category.id_comp] at hf
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hf]
  erw [← (HomotopyCategory.quotient C (.up ℤ)).commShiftIso_hom_naturality]
  simp only [← Functor.map_comp_assoc]
  simp only [← Category.assoc]
  apply (cancel_mono (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso
    (-(n : ℤ))).hom.app ((CochainComplex.singleFunctor C 0).obj (G.obj X)))).2
  rw [Functor.mapHomotopyCategory_map]
  erw [← Functor.map_comp]
  apply (HomotopyCategory.quotient C (.up ℤ)).congr_map
  have hm := G.mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app
    (-(n : ℤ)) n 0 (by simp) X
  apply (cancel_epi ((G.mapHomologicalComplex (.up ℤ)).map
    (((CochainComplex.singleFunctors B).shiftIso
      (-(n : ℤ)) n 0 (by simp)).hom.app X))).1
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp]
  erw [hm]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rfl

end CategoryTheory.Functor
