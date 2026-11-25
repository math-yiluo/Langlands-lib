/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import WeilConjectures.CategoryTheory.SingleHomologyShiftComparison
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Shifted single-object normalization

Source: Stacks Project, Tags 05TC (2) and 05TD (3).
(blueprint: new-lem-pc-derived-single-shift-normalization).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [EnoughInjectives C]
  [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D]
  (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S]

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

omit [EnoughInjectives C] in
private theorem derived_single_shift_inv (X : C) (n : ℤ) :
    ((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app X =
      DerivedCategory.Qh.map
        (((HomotopyCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app X) ≫
      (DerivedCategory.Qh.commShiftIso (-n)).hom.app
        ((HomotopyCategory.singleFunctor C 0).obj X) := by
  have hs := congr_app ((DerivedCategory.singleFunctorsPostcompQhIso C).inv.comm
    (-n) n 0 (by simp)) X
  have he (i : ℤ) : ((DerivedCategory.singleFunctorsPostcompQhIso C).inv.hom i).app X =
      𝟙 ((DerivedCategory.singleFunctor C i).obj X) := by
    change (𝟙 _) ≫ (𝟙 _) = 𝟙 _
    exact Category.id_comp _
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, he] at hs
  erw [Category.comp_id, Functor.map_id, Category.id_comp] at hs
  have hi : ((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app X =
      (((HomotopyCategory.singleFunctors C).postcomp DerivedCategory.Qh).shiftIso
        (-n) n 0 (by simp)).inv.app X := by
    apply (cancel_mono
      (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).hom.app X)).1
    erw [Iso.inv_hom_id_app, ← hs, Iso.inv_hom_id_app]
    rfl
  simpa only [SingleFunctors.postcomp_shiftIso_inv_app] using hi

omit [EnoughInjectives C] in
private theorem single_quotient_inverse_shift_int (X : C) (n : ℤ) :
    let e (i : ℤ) : (DerivedCategory.Plus.singleFunctor C i).obj X ≅
        DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor C i).obj X) :=
      DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.singleFunctorIsoCompQ C i).app X ≪≫
        (DerivedCategory.quotientCompQhIso C).symm.app _)
    let K₀ := (HomotopyCategory.Plus.singleFunctor C 0).obj X
    let h := ((HomotopyCategory.Plus.singleFunctors C).shiftIso
      (-n) n 0 (by simp)).inv.app X
    (e n).inv ≫ ((DerivedCategory.Plus.singleFunctors C).shiftIso
      (-n) n 0 (by simp)).inv.app X =
    DerivedCategory.Plus.Qh.map h ≫
      (DerivedCategory.Plus.Qh.commShiftIso (-n)).hom.app K₀ ≫
      ((e 0).inv)⟦-n⟧' := by
  intro e K₀ h
  have he (i : ℤ) : (e i).inv = 𝟙 ((DerivedCategory.Plus.singleFunctor C i).obj X) := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [e, Functor.preimageIso_inv, Functor.map_preimage, Iso.trans_inv]
    change (𝟙 _) ≫ (𝟙 _) = 𝟙 _
    exact Category.id_comp _
  rw [he, he]
  erw [Category.id_comp, Functor.map_id, Category.comp_id]
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.map_comp]
  simp only [DerivedCategory.Plus.singleFunctors, map_lift_single_shift_inv,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, Functor.map_id, Category.id_comp]
  simp only [derived_single_shift_inv, Category.assoc]
  change DerivedCategory.Qh.map
      (((HomotopyCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app X) ≫
    (DerivedCategory.Qh.commShiftIso (-n)).hom.app K₀.obj ≫
    (DerivedCategory.Plus.ι.commShiftIso (-n)).inv.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
    DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C).map h) ≫
    DerivedCategory.Plus.ι.map
      ((DerivedCategory.Plus.Qh.commShiftIso (-n)).hom.app K₀)
  have hq := Functor.CommShift.OfComp.map_iso_hom_app
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh)
      (fun K ↦ (DerivedCategory.Plus.Qh.obj K).property)) (-n) K₀
  simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.commShiftIso_comp_hom_app, Category.id_comp] at hq
  erw [hq]
  dsimp only [h]
  simp only [HomotopyCategory.Plus.singleFunctors, map_lift_single_shift_inv,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, Functor.map_id, Category.id_comp, Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rfl


omit [EnoughInjectives C]
  [HasDerivedCategory C] [PreservesFiniteLimits S] in
private theorem mapped_single_inverse_shift_int (X : C) (n : ℤ) :
    let K₀ := (HomotopyCategory.Plus.singleFunctor C 0).obj X
    let h := ((HomotopyCategory.Plus.singleFunctors C).shiftIso
      (-n) n 0 (by simp)).inv.app X
    (S.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫
      ((DerivedCategory.Plus.singleFunctors D).shiftIso
        (-n) n 0 (by simp)).inv.app (S.obj X) =
    DerivedCategory.Plus.Qh.map (S.mapHomotopyCategoryPlus.map h) ≫
      DerivedCategory.Plus.Qh.map
        ((S.mapHomotopyCategoryPlus.commShiftIso (-n)).hom.app K₀) ≫
      (DerivedCategory.Plus.Qh.commShiftIso (-n)).hom.app
        (S.mapHomotopyCategoryPlus.obj K₀) ≫
      ((S.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 X).hom)⟦-n⟧' := by
  intro K₀ h
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, mapHomotopyCategoryPlusSingleFunctorQhObjIso,
    Functor.preimageIso_hom, Functor.map_preimage]
  simp only [DerivedCategory.Plus.singleFunctors, map_lift_single_shift_inv,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, Functor.map_id, Category.id_comp]
  simp only [derived_single_shift_inv, Category.assoc]
  apply (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (-n)).hom.app
    ((DerivedCategory.Plus.singleFunctor D 0).obj (S.obj X)))).1
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  erw [DerivedCategory.Plus.ι.commShiftIso_hom_naturality]
  rw [Functor.map_preimage]
  have hq := Functor.CommShift.OfComp.map_iso_hom_app
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (HomotopyCategory.Plus.ι D ⋙ DerivedCategory.Qh)
      (fun K ↦ (DerivedCategory.Plus.Qh.obj K).property)) (-n)
      (S.mapHomotopyCategoryPlus.obj K₀)
  simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.commShiftIso_comp_hom_app, Category.id_comp] at hq
  erw [hq]
  erw [Functor.map_id, Category.id_comp]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  erw [Category.id_comp, Category.id_comp]
  change DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) n).app X).hom ≫
    DerivedCategory.Qh.map
      (((HomotopyCategory.singleFunctors D).shiftIso (-n) n 0 (by simp)).inv.app
        (S.obj X)) ≫ (DerivedCategory.Qh.commShiftIso (-n)).hom.app _ =
    DerivedCategory.Qh.map ((S.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.Plus.ι C).map h)) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι D).map
      ((S.mapHomotopyCategoryPlus.commShiftIso (-n)).hom.app K₀)) ≫
    DerivedCategory.Qh.map (((HomotopyCategory.Plus.ι D).commShiftIso
      (-n)).hom.app (S.mapHomotopyCategoryPlus.obj K₀)) ≫
    (DerivedCategory.Qh.commShiftIso (-n)).hom.app _ ≫
    (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0).app X).hom)⟦-n⟧'
  have hg := Functor.CommShift.OfComp.map_iso_hom_app
    ((HomotopyCategory.plus D).liftCompιIso
      (HomotopyCategory.Plus.ι C ⋙ S.mapHomotopyCategory (.up ℤ))
      (fun K ↦ (S.mapHomotopyCategoryPlus.obj K).property)) (-n) K₀
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
  have hp (i : ℤ) : DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) i).app X).hom =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) i).app X).hom) := by
    rfl
  rw [hp, hp]
  erw [← DerivedCategory.Qh.commShiftIso_hom_naturality]
  simp only [← Functor.map_comp_assoc]
  apply (cancel_mono ((DerivedCategory.Qh.commShiftIso (-n)).hom.app
    (((HomotopyCategory.singleFunctors D).functor 0).obj (S.obj X)))).2
  apply DerivedCategory.Qh.congr_map
  simp only [HomotopyCategory.singleFunctors, SingleFunctors.postcomp_shiftIso_inv_app]
  have hf := NatTrans.shift_app_comm
    (S.mapHomotopyCategoryFactors (.up ℤ)).hom (-n)
    ((CochainComplex.singleFunctor C 0).obj X)
  simp only [Functor.commShiftIso_comp_hom_app, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift, NatIso.ofComponents_hom_app, Iso.refl_hom, Functor.comp_obj] at hf
  erw [Functor.map_id, Category.comp_id, Category.id_comp] at hf
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hf]
  erw [← (HomotopyCategory.quotient D (.up ℤ)).commShiftIso_hom_naturality]
  simp only [← Functor.map_comp_assoc]
  simp only [← Category.assoc]
  apply (cancel_mono (((HomotopyCategory.quotient D (.up ℤ)).commShiftIso
    (-n)).hom.app ((CochainComplex.singleFunctor D 0).obj (S.obj X)))).2
  rw [Functor.mapHomotopyCategory_map]
  erw [← Functor.map_comp]
  apply (HomotopyCategory.quotient D (.up ℤ)).congr_map
  have hm := S.mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app
    (-n) n 0 (by simp) X
  apply (cancel_epi ((S.mapHomologicalComplex (.up ℤ)).map
    (((CochainComplex.singleFunctors C).shiftIso
      (-n) n 0 (by simp)).hom.app X))).1
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp]
  erw [hm]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rfl


omit [PreservesFiniteLimits S] in
private theorem rightDerivedPlusSingleUnit_shift_transport_int (X : C) (n : ℤ) :
    let M : CochainComplex.Plus C :=
      ⟨(CochainComplex.singleFunctor C n).obj X, n, inferInstance⟩
    let e : (DerivedCategory.Plus.singleFunctor C n).obj X ≅
        DerivedCategory.Plus.Q.obj M :=
      DerivedCategory.Plus.ι.preimageIso
        ((DerivedCategory.singleFunctorIsoCompQ C n).app X ≪≫
          (DerivedCategory.quotientCompQhIso C).symm.app _)
    let H₀ := DerivedCategory.Plus.homologyFunctor D 0
    let RG := S.rightDerivedFunctorPlus
    let c := Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).symm
      (RG ⋙ H₀.shift n) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
        (Functor.isoWhiskerRight (RG.commShiftIso (-n)) (H₀.shift n)) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0 ⋙ RG)
        (H₀.shiftIso (-n) n 0 (by ring))
    let d := Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors D).shiftIso (-n) n 0 (by simp)).symm
      (H₀.shift n) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor D 0)
        (H₀.shiftIso (-n) n 0 (by ring))
    (DerivedCategory.Plus.homologyFunctor D n).map
      (S.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj M)) ≫
      (DerivedCategory.Plus.homologyFunctor D n).map (S.rightDerivedFunctorPlus.map e.inv) ≫
      c.hom.app X =
    (DerivedCategory.Plus.homologyFunctor D n).map
      (S.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫
      d.hom.app (S.obj X) ≫ H₀.map (S.rightDerivedPlusSingleUnit X) := by
  intro M e H₀ RG c d
  dsimp only [M, e, H₀, RG, c, d]
  let K₀ := (HomotopyCategory.Plus.singleFunctor C 0).obj X
  let h := ((HomotopyCategory.Plus.singleFunctors C).shiftIso
    (-n) n 0 (by simp)).inv.app X
  let eₙ : (DerivedCategory.Plus.singleFunctor C n).obj X ≅
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor C n).obj X) :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.singleFunctorIsoCompQ C n).app X ≪≫
        (DerivedCategory.quotientCompQhIso C).symm.app _)
  let sB := ((DerivedCategory.Plus.singleFunctors C).shiftIso
    (-n) n 0 (by simp)).inv.app X
  let sC := ((DerivedCategory.Plus.singleFunctors D).shiftIso
    (-n) n 0 (by simp)).inv.app (S.obj X)
  let F := S.rightDerivedFunctorPlus
  let U := S.rightDerivedFunctorPlusUnith
  have ht := single_quotient_inverse_shift_int X n
  have hs := mapped_single_inverse_shift_int S X n
  have hu := U.naturality h
  have hc := NatTrans.shift_app_comm U (-n) K₀
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at hc
  simp only [Functor.comp_map, Functor.comp_obj] at hu
  have hd : U.app ((HomotopyCategory.Plus.singleFunctor C n).obj X) ≫
      F.map eₙ.inv ≫ F.map sB ≫
        (F.commShiftIso (-n)).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
      (S.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫ sC ≫
        (S.rightDerivedPlusSingleUnit X)⟦-n⟧' := by
    rw [← F.map_comp_assoc, ht]
    simp only [F.map_comp, Category.assoc]
    rw [F.commShiftIso_hom_naturality]
    erw [← reassoc_of% hu]
    erw [← reassoc_of% hc]
    erw [reassoc_of% hs]
    simp only [rightDerivedPlusSingleUnit, Functor.map_comp]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
    rfl
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Iso.symm_hom,
    Functor.comp_map, Category.assoc]
  change (DerivedCategory.Plus.homologyFunctor D n).map (U.app _) ≫
    (DerivedCategory.Plus.homologyFunctor D n).map (F.map eₙ.inv) ≫
    (DerivedCategory.Plus.homologyFunctor D n).map (F.map sB) ≫
    (DerivedCategory.Plus.homologyFunctor D n).map
      ((F.commShiftIso (-n)).hom.app _) ≫ _ =
    (DerivedCategory.Plus.homologyFunctor D n).map
      (S.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫
    (DerivedCategory.Plus.homologyFunctor D n).map sC ≫ _ ≫ _
  simp only [← Functor.map_comp_assoc] at hd ⊢
  rw [hd]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun f ↦
    (DerivedCategory.Plus.homologyFunctor D n).map
      (S.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫
    (DerivedCategory.Plus.homologyFunctor D n).map sC ≫ f)
    (((DerivedCategory.Plus.homologyFunctor D 0).shiftIso
      (-n) n 0 (by ring)).hom.naturality (S.rightDerivedPlusSingleUnit X))


/-- The actual bounded-below derived unit on an object in degree n.
Source: Stacks Project, Tag 05TD (3).
(blueprint: new-lem-pc-derived-single-shift-normalization). -/
noncomputable def rightDerivedPlusSingleUnitAt (n : ℤ) (Y : C) :
    (DerivedCategory.Plus.singleFunctor D n).obj (S.obj Y) ⟶
      S.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C n).obj Y) :=
  (S.mapHomotopyCategoryPlusSingleFunctorQhObjIso n Y).inv ≫
    S.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor C n).obj Y) ≫
    S.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.ι.preimageIso
        (X := (DerivedCategory.Plus.singleFunctor C n).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor C n).obj Y))
        ((DerivedCategory.singleFunctorIsoCompQ C n).app Y ≪≫
          (DerivedCategory.quotientCompQhIso C).symm.app _)).inv

/-- Homology of the actual unit on a single object in degree n.
Source: Stacks Project, Tag 05TD (3).
(blueprint: new-lem-pc-derived-single-shift-normalization). -/
noncomputable def rightDerivedPlusSingleUnitHomologyAt (n : ℤ) (Y : C) :
    S.obj Y ⟶ (DerivedCategory.Plus.homologyFunctor D n).obj
      (S.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C n).obj Y)) :=
  (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).inv.app (S.obj Y) ≫
    (DerivedCategory.Plus.homologyFunctor D n).map (S.rightDerivedPlusSingleUnitAt n Y)

/-- The shifted single-object isomorphism used in the specified bottom comparison.
Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-single-shift-normalization). -/
noncomputable def rightDerivedPlusSingleShiftIso (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ⋙ S.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor D n ≅ S := by
  let R := S.rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor D n
  let H₀ := DerivedCategory.Plus.homologyFunctor D 0
  exact
    Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by omega)).symm
      (R ⋙ H) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (Functor.isoWhiskerRight (R.commShiftIso (-n)) H) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0 ⋙ R)
      (H₀.shiftIso (-n) n 0 (by omega)) ≪≫
    S.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0 ≪≫
    S.rightDerivedZeroIsoSelf

/-- Shift normalization of the actual unit on a single object.

Source: Stacks Project, Tag 05TC (2), using the degree-zero identification
in Tag 05TD (3).
(blueprint: new-lem-pc-derived-single-shift-normalization).

Proof: Shift the single object in degree n by -n to the single object in
degree zero. The quotient/single comparison and the actual derived unit
commute with this shift; use the commShift square of the right-derived unit.
Apply homology with its shift isomorphism. Naturality of these three
isomorphisms identifies the displayed composite with the degree-zero
single-unit composite. The proved single-unit homology comparison makes
this toRightDerivedZero followed by rightDerivedZeroIsoSelf.hom. These
are inverse maps, because S is left exact. Cancel the shift isomorphisms
on source and target to obtain the identity in degree n. This works for
negative n as well; n=0 is precisely the established degree-zero calculation. -/
theorem rightDerivedPlusSingleUnitHomologyAt_comp_shiftIso (n : ℤ) (Y : C) :
    S.rightDerivedPlusSingleUnitHomologyAt n Y ≫
      (S.rightDerivedPlusSingleShiftIso n).hom.app Y = 𝟙 (S.obj Y) := by
  let H₀ := DerivedCategory.Plus.homologyFunctor D 0
  let R := S.rightDerivedFunctorPlus
  let c := Functor.isoWhiskerRight
    ((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).symm
    (R ⋙ H₀.shift n) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (Functor.isoWhiskerRight (R.commShiftIso (-n)) (H₀.shift n)) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0 ⋙ R)
      (H₀.shiftIso (-n) n 0 (by ring))
  let d := Functor.isoWhiskerRight
    ((DerivedCategory.Plus.singleFunctors D).shiftIso (-n) n 0 (by simp)).symm
    (H₀.shift n) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor D 0)
      (H₀.shiftIso (-n) n 0 (by ring))
  have hd :
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).inv.app (S.obj Y) ≫
        d.hom.app (S.obj Y) =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (S.obj Y) := by
    apply (cancel_mono
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).hom.app (S.obj Y))).1
    rw [Category.assoc]
    rw [show d.hom.app (S.obj Y) ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).hom.app (S.obj Y) =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).hom.app (S.obj Y) from
        singleFunctor_homology_shift_comparison (S.obj Y) n]
    simp
  have ht := rightDerivedPlusSingleUnit_shift_transport_int S Y n
  dsimp only at ht
  have hunit : S.rightDerivedPlusSingleUnitHomologyAt n Y ≫ c.hom.app Y =
      S.rightDerivedPlusSingleUnitHomology Y := by
    dsimp only [rightDerivedPlusSingleUnitHomologyAt, rightDerivedPlusSingleUnitAt]
    simp only [Functor.map_comp, Category.assoc]
    change (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).inv.app (S.obj Y) ≫
      (DerivedCategory.Plus.homologyFunctor D n).map
        (S.mapHomotopyCategoryPlusSingleFunctorQhObjIso n Y).inv ≫
      ((DerivedCategory.Plus.homologyFunctor D n).map
        (S.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor C n).obj Y)) ≫
      (DerivedCategory.Plus.homologyFunctor D n).map
        (S.rightDerivedFunctorPlus.map _) ≫ c.hom.app Y) = _
    erw [ht]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    change _ ≫ d.hom.app (S.obj Y) ≫ H₀.map (S.rightDerivedPlusSingleUnit Y) = _
    rw [← Category.assoc, hd]
    rfl
  have hcmp : (S.rightDerivedPlusSingleShiftIso n).hom.app Y =
      c.hom.app Y ≫
        (S.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app Y ≫
        S.rightDerivedZeroIsoSelf.hom.app Y := by
    simp only [rightDerivedPlusSingleShiftIso, c, Iso.trans_hom, NatTrans.comp_app,
      Category.assoc]
    rfl
  rw [hcmp]
  erw [reassoc_of% hunit, reassoc_of%
    (S.rightDerivedPlusSingleUnitHomology_comp_comparison Y)]
  exact S.rightDerivedZeroIsoSelf_inv_hom_id_app Y

end CategoryTheory.Functor
