/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomComparison
public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement

/-! # Evaluation of the fixed native small-site Hom comparison

## References

* Stacks 03D6 and 03EO
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Opposite
open CategoryTheory.TwistedActionRingedSite
open WeilConjectures.WeilFrobeniusAction
namespace AlgebraicGeometry.ProEtale.NativeFrobenius

/-- The section counit for the specified small-site-to-native equivalence. -/
noncomputable def sectionCounit (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    (equivalence Y l).functor ⋙ (adicSectionModuleEquivalence l Y).functor ≅
      SheafOfModules.SmallSite.restriction (Scheme.ProEt.topology Y) (comparisonRing l Y) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (adicSectionModuleEquivalence l Y).counitIso ≪≫
      Functor.rightUnitor _

private theorem inverseComparison_map
    {A B : Type*} [Category A] [Category B] (E : B ≌ A)
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B)
    (h : HB ⋙ E.functor ≅ E.functor.op.prod E.functor ⋙ HA) (M N : A) :
    E.functor.map ((HomComparison.inverseHomComparison E HA HB h).hom.app (op M, N)) ≫
        h.hom.app (op (E.inverse.obj M), E.inverse.obj N) =
      E.counitIso.hom.app (HA.obj (op M, N)) ≫
        HA.map (show (op M, N) ⟶
          (op (E.functor.obj (E.inverse.obj M)), E.functor.obj (E.inverse.obj N)) from
            ((E.counitIso.hom.app M).op, E.counitIso.inv.app N)) := by
  simp only [HomComparison.inverseHomComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp,
    Functor.map_comp, Functor.comp_map]
  rw [← E.counit_app_functor]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [Category.assoc]
  change E.functor.map (E.inverse.map (HA.map
      ((NatIso.prod (NatIso.op E.counitIso.symm) E.counitIso).inv.app (op M, N)))) ≫
    E.functor.map (E.inverse.map (h.inv.app (op (E.inverse.obj M), E.inverse.obj N))) ≫
      E.counitIso.hom.app _ ≫ h.hom.app (op (E.inverse.obj M), E.inverse.obj N) = _
  erw [E.counit_naturality_assoc, Iso.inv_hom_id_app, Category.comp_id,
    E.counit_naturality]
  rfl

private theorem inverseComparison_precompose
    {A B : Type*} [Category A] [Category B] (E : B ≌ A)
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B)
    (h : HB ⋙ E.functor ≅ E.functor.op.prod E.functor ⋙ HA)
    (Z M N : A) (f : Z ⟶ HA.obj (op M, N)) :
    E.functor.map (E.inverse.map f ≫
        (HomComparison.inverseHomComparison E HA HB h).hom.app (op M, N)) ≫
      h.hom.app (op (E.inverse.obj M), E.inverse.obj N) =
    E.counitIso.hom.app Z ≫ f ≫
      HA.map (show (op M, N) ⟶
          (op (E.functor.obj (E.inverse.obj M)), E.functor.obj (E.inverse.obj N)) from
            ((E.counitIso.hom.app M).op, E.counitIso.inv.app N)) := by
  rw [Functor.map_comp, Category.assoc, inverseComparison_map]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t ↦ t ≫ HA.map
      (show (op M, N) ⟶
          (op (E.functor.obj (E.inverse.obj M)), E.functor.obj (E.inverse.obj N)) from
            ((E.counitIso.hom.app M).op, E.counitIso.inv.app N)))
      (E.counit_naturality f)).trans (Category.assoc _ _ _))

section
attribute [local irreducible] comparisonModuleFunctor
  comparisonRing SheafOfModules.homObjMap

private theorem homComparison_map (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (H : AdicModuleHomComparisonCore l Y) (M N : Modules (ring Y l)) :
    (comparisonModuleFunctor l Y).map (homComparison Y l H M N).hom ≫
        (H.homIso ((equivalence Y l).functor.obj M)).hom.app
          ((equivalence Y l).functor.obj N) =
      (sectionCounit Y l).hom.app (SheafOfModules.homObj (R := ring Y l) M N) ≫
        (SheafOfModules.SmallSite.homIso (Scheme.ProEt.topology Y)
          (comparisonRing l Y) M N).hom ≫
        SheafOfModules.homObjMap (R := comparisonRing l Y)
          ((sectionCounit Y l).hom.app M) ((sectionCounit Y l).inv.app N) := by
  let E := adicSectionModuleEquivalence l Y
  let Q := SheafOfModules.SmallSite.restriction (Scheme.ProEt.topology Y) (comparisonRing l Y)
  have h := inverseComparison_precompose E
    (Functor.uncurry.obj (SheafOfModules.homFunctor (comparisonRing l Y)))
    (nativeHom Y l) (forwardHomComparison Y l H)
    (Q.obj (SheafOfModules.homObj (R := ring Y l) M N)) (Q.obj M) (Q.obj N)
    (SheafOfModules.SmallSite.homIso (Scheme.ProEt.topology Y)
      (comparisonRing l Y) M N).hom
  simp only [Functor.uncurry_obj_map, SheafOfModules.homFunctor_map_app,
    SheafOfModules.homFunctor_obj_map, SheafOfModules.homObjMap_comp_homObjMap,
    Category.id_comp] at h
  exact h

end

/-- The fixed Hom comparison is normalized by evaluation on the identity slice. -/
theorem comparison_evaluation (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (H : AdicModuleHomComparisonCore l Y) (M N : Modules (ring Y l))
    (V : Y.ProEtᵒᵖ)
    (z : ((equivalence Y l).functor.obj
      (SheafOfModules.homObj (R := ring Y l) M N)).X.obj.obj V)
    (x : ((equivalence Y l).functor.obj M).X.obj.obj V) :
    ((sectionCounit Y l).hom.app N).val.app V
      (adicComparisonEval ((equivalence Y l).functor.obj M) ((equivalence Y l).functor.obj N)
        V ((homComparison Y l H M N).hom.hom.hom.app V z) x) =
      ((((sectionCounit Y l).hom.app (SheafOfModules.homObj (R := ring Y l) M N)).val.app V z).app
        (op (Over.mk (AsSmall.up.map (𝟙 V.unop)))))
          (((sectionCounit Y l).hom.app M).val.app V x) := by
  have h := congrArg (fun k ↦ ((k.val.app V z).app (op (Over.mk (𝟙 V.unop)))) x)
    (homComparison_map Y l H M N)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at h
  change ((((H.homIso ((equivalence Y l).functor.obj M)).hom.app
      ((equivalence Y l).functor.obj N)).val.app V
        ((homComparison Y l H M N).hom.hom.hom.app V z)).app
          (op (Over.mk (𝟙 V.unop)))) x =
    ((sectionCounit Y l).inv.app N).val.app V
      (((((sectionCounit Y l).hom.app
        (SheafOfModules.homObj (R := ring Y l) M N)).val.app V z).app
          (op (Over.mk (AsSmall.up.map (𝟙 V.unop)))))
            (((sectionCounit Y l).hom.app M).val.app V x)) at h
  have hH := H.evaluation ((equivalence Y l).functor.obj M)
    ((equivalence Y l).functor.obj N) V
      ((homComparison Y l H M N).hom.hom.hom.app V z) x
  simp only [AddEquiv.refl_apply] at hH
  rw [← hH] at h
  rw [h]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.val.app V) ((sectionCounit Y l).app N).inv_hom_id) _

end AlgebraicGeometry.ProEtale.NativeFrobenius
