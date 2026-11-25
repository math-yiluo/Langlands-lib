/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
import WeilConjectures.AlgebraicGeometry.ModuleRingedToposDerivedComparison
import WeilConjectures.AlgebraicGeometry.SectionTensorConjugateComputation
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison

/-! # Transport of normalized scalar tensor comparisons to section modules

(auxiliary; not a blueprint node)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  ModuleRingedComparison.tensor ModuleRingedComparison.derivedEquivalence
  ModuleRingedComparison.ordinaryTensorComparison
  ModuleRingedComparison.tensorComparison
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private def cancelSectionIso
    {C D A : Type*} [Category* C] [Category* D] [Category* A]
    (E : C ≌ D) {F G : D ⥤ A} (i : E.functor ⋙ F ≅ E.functor ⋙ G) : F ≅ G :=
  (E.congrLeft : (C ⥤ A) ≌ (D ⥤ A)).fullyFaithfulInverse.preimageIso i

private theorem cancelSectionIso_hom
    {C D A : Type*} [Category* C] [Category* D] [Category* A]
    (E : C ≌ D) {F G : D ⥤ A} (i : E.functor ⋙ F ≅ E.functor ⋙ G) (M : C) :
    (cancelSectionIso E i).hom.app (E.functor.obj M) = i.hom.app M := by
  have h := (E.congrLeft : (C ⥤ A) ≌ (D ⥤ A)).fullyFaithfulInverse.map_preimage i.hom
  exact congrArg (fun f ↦ f.app M) h

private def conjugateComparison
    {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
    (E : C ≌ D) (E' : C' ⥤ D') (F : C ⥤ C') (H : C' ⥤ C)
    (G : D ⥤ D') (U : D' ⥤ D) (K : C ⥤ C) (L : D ⥤ D)
    (s : F ⋙ E' ≅ E.functor ⋙ G) (r : H ⋙ E.functor ≅ E' ⋙ U)
    (t : F ⋙ H ≅ K) (k : K ⋙ E.functor ≅ E.functor ⋙ L) :
    E.functor ⋙ (G ⋙ U) ≅ E.functor ⋙ L :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight s.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F r.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight t _ ≪≫ k

private theorem conjugateComparison_eq
    {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
    (E : C ≌ D) (E' : C' ⥤ D') (F : C ⥤ C') (H : C' ⥤ C)
    (G : D ⥤ D') (U : D' ⥤ D) (K : C ⥤ C) (L : D ⥤ D)
    (s : F ⋙ E' ≅ E.functor ⋙ G) (r : H ⋙ E.functor ≅ E' ⋙ U)
    (t : F ⋙ H ≅ K) (k : K ⋙ E.functor ≅ E.functor ⋙ L) (M : C) :
    E.functor.map (t.hom.app M) ≫ k.hom.app M =
      r.hom.app (F.obj M) ≫ U.map (s.hom.app M) ≫
        (cancelSectionIso E (conjugateComparison E E' F H G U K L s r t k)).hom.app
          (E.functor.obj M) := by
  rw [cancelSectionIso_hom]
  dsimp only [conjugateComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj]
  simp only [Category.id_comp, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp

attribute [local irreducible] cancelSectionIso

set_option linter.unusedSectionVars false

private def ordinaryRightComparison (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    tensorRight (B₀ a T) ⋙ (ModuleRingedComparison.equivalence Λ T).functor ≅
      (ModuleRingedComparison.equivalence Λ T).functor ⋙
        tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) := by
  refine NatIso.ofComponents
    (fun M ↦ ModuleRingedComparison.ordinaryTensorComparison Λ T M (B₀ a T)) ?_
  intro M N f
  have h := (ModuleRingedComparison.ordinary_monoidal Λ T).1
    M N (B₀ a T) (B₀ a T) f (𝟙 _)
  change (ModuleRingedComparison.equivalence Λ T).functor.map (f ⊗ₘ 𝟙 _) ≫ _ =
    _ ≫ ((ModuleRingedComparison.equivalence Λ T).functor.map f ⊗ₘ
      (ModuleRingedComparison.equivalence Λ T).functor.map (𝟙 _)) at h
  rw [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at h
  exact h

attribute [local irreducible] ordinaryRightComparison

private def ordinaryConjugate (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (t : TensorNormalization a T) :
    (ModuleRingedComparison.equivalence Λ T).functor ⋙
        (s.pair.extension ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap a T))) ≅
      (ModuleRingedComparison.equivalence Λ T).functor ⋙
        tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) :=
  conjugateComparison (ModuleRingedComparison.equivalence Λ T)
    (ModuleRingedComparison.equivalence Λ' T).functor (extension a T) (V₀ a T)
    s.pair.extension _ _ _ s.ordinary s.restriction t.ordinary (ordinaryRightComparison a T)

attribute [local irreducible] ordinaryConjugate

private def ordinarySectionComparison (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (t : TensorNormalization a T) :=
  cancelSectionIso (ModuleRingedComparison.equivalence Λ T) (ordinaryConjugate a T s t)

attribute [local irreducible] ordinarySectionComparison

private def derivedRightComparison (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    tensorRight (B a T) ⋙ (ModuleRingedComparison.derivedEquivalence Λ T).functor ≅
      (ModuleRingedComparison.derivedEquivalence Λ T).functor ⋙ sectionScalarTensor a T :=
  NatIso.ofComponents
    (fun M ↦ (ModuleRingedComparison.tensorComparison Λ T).app (M, B a T)) (by
      intro M N f
      have h := (ModuleRingedComparison.tensorComparison Λ T).hom.naturality
        (Prod.mkHom f (𝟙 (B a T)))
      change (ModuleRingedComparison.derivedEquivalence Λ T).functor.map
        (((CondensedRing.derivedTensor Λ T).map f).app (B a T) ≫
          ((CondensedRing.derivedTensor Λ T).obj N).map (𝟙 (B a T))) ≫ _ = _ at h
      change (ModuleRingedComparison.derivedEquivalence Λ T).functor.map
        (((CondensedRing.derivedTensor Λ T).map f).app (B a T)) ≫ _ = _ at ⊢
      simp only [sectionScalarTensor, Functor.comp_map, Functor.prod'_map,
        Functor.id_map, Functor.const_obj_map, Functor.prod_map,
        Functor.comp_obj, Functor.prod_obj, Functor.prod'_obj, Functor.id_obj,
        Functor.const_obj_obj, CategoryTheory.Functor.map_id, Category.comp_id,
        Iso.app_hom] at h ⊢
      run_tac Lean.Elab.Tactic.withMainContext do
        let some hd := (← Lean.getLCtx).findFromUserName? `h
          | Lean.throwError "missing tensor naturality proof"
        (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
        Lean.Elab.Tactic.replaceMainGoal [])

private theorem derivedRightComparison_hom (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (M : DerivedCategory (Modules Λ T)) :
    (derivedRightComparison a T).hom.app M =
      (ModuleRingedComparison.tensorComparison Λ T).hom.app (M, B a T) := by
  simp only [derivedRightComparison, NatIso.ofComponents_hom_app]
  rfl

attribute [local irreducible] derivedRightComparison

private def derivedConjugate (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (t : TensorNormalization a T) :
    (ModuleRingedComparison.derivedEquivalence Λ T).functor ⋙
        (s.pair.derived ⋙ SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap a T))) ≅
      (ModuleRingedComparison.derivedEquivalence Λ T).functor ⋙ sectionScalarTensor a T :=
  conjugateComparison (ModuleRingedComparison.derivedEquivalence Λ T)
    (ModuleRingedComparison.derivedEquivalence Λ' T).functor (D a T) (V a T)
    s.pair.derived _ _ _ s.derived (sectionScalarRestriction a T s)
    t.derived (derivedRightComparison a T)

attribute [local irreducible] derivedConjugate

private def derivedSectionComparison (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (t : TensorNormalization a T) :=
  cancelSectionIso (ModuleRingedComparison.derivedEquivalence Λ T) (derivedConjugate a T s t)

private theorem derivedSectionComparison_conjugation (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (s : SectionScalarComparison a T) (t : TensorNormalization a T)
    (M : DerivedCategory (Modules Λ T)) :
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.map (t.derived.hom.app M) ≫
        (ModuleRingedComparison.tensorComparison Λ T).hom.app (M, B a T) =
      (sectionScalarRestriction a T s).hom.app ((D a T).obj M) ≫
        (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap a T))).map
              (s.derived.hom.app M) ≫
        (derivedSectionComparison a T s t).hom.app
          ((ModuleRingedComparison.derivedEquivalence Λ T).functor.obj M) := by
  have h := conjugateComparison_eq (ModuleRingedComparison.derivedEquivalence Λ T)
    (ModuleRingedComparison.derivedEquivalence Λ' T).functor (D a T) (V a T)
    s.pair.derived _ _ _ s.derived (sectionScalarRestriction a T s)
    t.derived (derivedRightComparison a T) M
  rw [← derivedRightComparison_hom a T M]
  rw [derivedSectionComparison, cancelSectionIso_hom]
  rw [cancelSectionIso_hom] at h
  simpa only [derivedConjugate] using h

private theorem ordinarySectionComparison_conjugation (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (s : SectionScalarComparison a T) (t : TensorNormalization a T)
    (M : Modules Λ T) :
    (ModuleRingedComparison.equivalence Λ T).functor.map (t.ordinary.hom.app M) ≫
        (ordinaryRightComparison a T).hom.app M =
      (s.restriction.hom.app ((extension a T).obj M)) ≫
        (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap a T))).map
              (s.ordinary.hom.app M) ≫
        (ordinarySectionComparison a T s t).hom.app
          ((ModuleRingedComparison.equivalence Λ T).functor.obj M) := by
  simpa only [ordinarySectionComparison, ordinaryConjugate] using
    conjugateComparison_eq (ModuleRingedComparison.equivalence Λ T)
    (ModuleRingedComparison.equivalence Λ' T).functor (extension a T) (V₀ a T)
    s.pair.extension _ _ _ s.ordinary s.restriction t.ordinary (ordinaryRightComparison a T) M

private theorem internal_tensor_generator (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (t : TensorNormalization a T) (M : Modules Λ T)
    (U : T.ProEtᵒᵖ) (z : (condensedRingObj Λ' T).obj.obj U) (x : M.X.obj.obj U) :
    ((t.ordinary.hom.app M).hom.hom.app U)
      (CategoryTheory.InternalAbelianSheafModule.internalScalarGenerator
        (Scheme.ProEt.topology T) (coefficientMap a T) M U z x) =
      ModuleRingedComparison.internalPureTensor Λ T M (B₀ a T) U x z := by
  let J := Scheme.ProEt.topology T
  let R := condensedRingObj Λ T
  let S := condensedRingObj Λ' T
  let F := sheafToPresheaf J AddCommGrpCat.{u + 1}
  have hc : Mod.extendπ (coefficientMap a T) M ≫
      (Mod.extendForgetTensorObjIso (coefficientMap a T) M).hom =
        Mod.tensorObjπ (B₀ a T) M :=
    Mod.extendπ_extendDescHom _ _ _
  have h := congrArg (fun k ↦ Functor.LaxMonoidal.μ F S M.X ≫ F.map k) hc
  simp only [Functor.map_comp] at h
  have he := congrArg (fun k ↦ (k.app U).hom (z ⊗ₜ[ℤ] x)) h
  change ((Mod.extendForgetTensorObjIso (coefficientMap a T) M).hom.hom.app U)
      (CategoryTheory.InternalAbelianSheafModule.internalScalarGenerator
        J (coefficientMap a T) M U z x) =
    CategoryTheory.InternalAbelianSheafModule.comparison_internalTmul
      J R (B₀ a T) M U z x at he
  rw [t.ordinary_hom]
  change ((β_ (B₀ a T) M).hom.hom.hom.app U)
    (((Mod.extendForgetTensorObjIso (coefficientMap a T) M).hom.hom.app U) _) = _
  rw [he]
  exact CategoryTheory.InternalAbelianSheafModule.comparison_internalTmul_braiding
    J R (B₀ a T) M U z x

private theorem ordinary_generator_image (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (s : SectionScalarComparison a T)
    (hs : SectionScalarNormalized a T s) (t : TensorNormalization a T)
    (M : Modules Λ T) (U : T.ProEtᵒᵖ)
    (z : (condensedRingObj Λ' T).obj.obj U) (x : M.X.obj.obj U) :
    ((ordinarySectionComparison a T s t).hom.app
        ((ModuleRingedComparison.equivalence Λ T).functor.obj M)).val.app U
      ((s.ordinary.hom.app M).val.app U
        (CategoryTheory.InternalAbelianSheafModule.internalScalarGenerator
          (Scheme.ProEt.topology T) (coefficientMap a T) M U z x)) =
      ModuleRingedComparison.sectionPureTensor Λ T
        ((ModuleRingedComparison.equivalence Λ T).functor.obj M)
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) U x z := by
  have h := congrArg (fun k ↦ k.val.app U
    (CategoryTheory.InternalAbelianSheafModule.internalScalarGenerator
      (Scheme.ProEt.topology T) (coefficientMap a T) M U z x))
    (ordinarySectionComparison_conjugation a T s t M)
  change ((ordinaryRightComparison a T).hom.app M).val.app U
    (((t.ordinary.hom.app M).hom.hom.app U) _) =
      ((ordinarySectionComparison a T s t).hom.app
        ((ModuleRingedComparison.equivalence Λ T).functor.obj M)).val.app U
          ((s.ordinary.hom.app M).val.app U
            ((s.restriction.hom.app ((extension a T).obj M)).val.app U _)) at h
  have hr := hs.1 ((extension a T).obj M) U
    (CategoryTheory.InternalAbelianSheafModule.internalScalarGenerator
      (Scheme.ProEt.topology T) (coefficientMap a T) M U z x)
  have ht := internal_tensor_generator a T t M U z x
  have h' := congrArg
    (fun y ↦ ((ordinarySectionComparison a T s t).hom.app
      ((ModuleRingedComparison.equivalence Λ T).functor.obj M)).val.app U
        ((s.ordinary.hom.app M).val.app U y)) hr
  have h'' := congrArg (((ordinaryRightComparison a T).hom.app M).val.app U) ht
  have hp : ((ordinaryRightComparison a T).hom.app M).val.app U
      (ModuleRingedComparison.internalPureTensor Λ T M (B₀ a T) U x z) =
      ModuleRingedComparison.sectionPureTensor Λ T
        ((ModuleRingedComparison.equivalence Λ T).functor.obj M)
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) U x z := by
    have hp := (ModuleRingedComparison.ordinaryTensorComparison_existsUnique Λ T M
      (B₀ a T)).exists.choose_spec U x z
    simp only [ordinaryRightComparison, NatIso.ofComponents_hom_app,
      ModuleRingedComparison.ordinaryTensorComparison, Functor.comp_obj,
      tensorRight, Functor.flip_obj_obj] at ⊢
    run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `hp
        | Lean.throwError "missing pure tensor proof"
      (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
      Lean.Elab.Tactic.replaceMainGoal []
  exact (h'.symm.trans h.symm).trans (h''.trans hp)

private def sectionGenerator (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (M : ModuleRingedComparison.modules Λ T)
    (U : T.ProEtᵒᵖ) (z : (ModuleRingedComparison.ring Λ' T).obj.obj U)
    (x : M.val.obj U) : (s.pair.extension.obj M).val.obj U :=
  (eqToHom (s.pair.extension_obj M).symm).val.app U
    ((toSheafify (Scheme.ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf
        (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology T) (coefficientMap a T)) M).presheaf).app U
        (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,
          ((CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap a T)).hom.app U).hom] x))

private theorem sectionGenerator_naturality (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (s : SectionScalarComparison a T)
    {M N : ModuleRingedComparison.modules Λ T} (f : M ⟶ N)
    (U : T.ProEtᵒᵖ) (z : (ModuleRingedComparison.ring Λ' T).obj.obj U) (x : M.val.obj U) :
    (s.pair.extension.map f).val.app U (sectionGenerator a T s M U z x) =
      sectionGenerator a T s N U z (f.val.app U x) := by
  let φ := CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (coefficientMap a T)
  let p : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ M f }
  have h := congrArg (fun g ↦ g.app U (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,
    (φ.hom.app U).hom] x))
    (toSheafify_naturality (Scheme.ProEt.topology T)
      ((PresheafOfModules.toPresheaf _).map p))
  dsimp only [sectionGenerator]
  rw [s.pair.extension_map]
  change (eqToHom (s.pair.extension_obj N).symm).val.app U
    ((SheafOfModules.changeOfRingsHom φ M f).val.app U
      (((eqToHom (s.pair.extension_obj M).symm ≫
        eqToHom (s.pair.extension_obj M)).val.app U) _)) = _
  simp only [eqToHom_trans, eqToHom_refl, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]
  apply congrArg ((eqToHom (s.pair.extension_obj N).symm).val.app U)
  change (toSheafify (Scheme.ProEt.topology T)
    (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
      ((ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
        (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U, (φ.hom.app U).hom] x)) = _ at h
  have hh := h.symm
  simp only [ModuleCat.ExtendScalars.map_tmul, SheafOfModules.changeOfRingsHom,
    PresheafOfModules.sheafification_map, NatTrans.comp_app,
    AddCommGrpCat.comp_apply, PresheafOfModules.sheafifyMap,
    PresheafOfModules.homMk, CategoryTheory.sheafifyMap, ModuleCat.hom_ofHom] at hh ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hh
      | Lean.throwError "missing sheafification naturality proof"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

private theorem ordinary_generator (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (s : SectionScalarComparison a T)
    (hs : SectionScalarNormalized a T s) (t : TensorNormalization a T)
    (M : ModuleRingedComparison.modules Λ T) (U : T.ProEtᵒᵖ)
    (z : (ModuleRingedComparison.ring Λ' T).obj.obj U) (x : M.val.obj U) :
    ((ordinarySectionComparison a T s t).hom.app M).val.app U
        (sectionGenerator a T s M U z x) =
      ModuleRingedComparison.sectionPureTensor Λ T M
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) U x z := by
  change (condensedRingObj Λ' T).obj.obj U at z
  let E := ModuleRingedComparison.equivalence Λ T
  let N := E.functor.objPreimage M
  let i : E.functor.obj N ≅ M := E.functor.objObjPreimageIso M
  clear_value i
  clear_value N
  let y := i.inv.val.app U x
  have hxy : i.hom.val.app U y = x := by
    exact congrArg (fun f ↦ f.val.app U x) i.inv_hom_id
  have hgen : sectionGenerator a T s (E.functor.obj N) U z y =
      (s.ordinary.hom.app N).val.app U
        (CategoryTheory.InternalAbelianSheafModule.internalScalarGenerator
          (Scheme.ProEt.topology T) (coefficientMap a T) N U z y) := by
    have h := congrArg ((eqToHom (s.pair.extension_obj (E.functor.obj N)).symm).val.app U)
      (hs.2.1 N U z y)
    change ((eqToHom (s.pair.extension_obj (E.functor.obj N)) ≫
      eqToHom (s.pair.extension_obj (E.functor.obj N)).symm).val.app U) _ =
        sectionGenerator a T s (E.functor.obj N) U z y at h
    simpa only [eqToHom_trans, eqToHom_refl, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] using h.symm
  have hn := congrArg (fun f ↦ f.val.app U
    (sectionGenerator a T s (E.functor.obj N) U z y))
    ((ordinarySectionComparison a T s t).hom.naturality i.hom)
  change ((ordinarySectionComparison a T s t).hom.app M).val.app U
      ((s.pair.extension.map i.hom).val.app U _) =
    ((tensorRight (E.functor.obj (B₀ a T))).map i.hom).val.app U
      (((ordinarySectionComparison a T s t).hom.app (E.functor.obj N)).val.app U _) at hn
  have hgin := (sectionGenerator_naturality a T s i.hom U z y).trans
    (congrArg (sectionGenerator a T s M U z) hxy)
  have himg := (congrArg
    (((ordinarySectionComparison a T s t).hom.app (E.functor.obj N)).val.app U) hgen).trans
      (ordinary_generator_image a T s hs t N U z y)
  have h := (congrArg (((ordinarySectionComparison a T s t).hom.app M).val.app U)
    hgin).symm.trans (hn.trans (congrArg
      (((tensorRight (E.functor.obj (B₀ a T))).map i.hom).val.app U) himg))
  have hp := CategoryTheory.InternalAbelianSheafModule.comparison_sectionTmul_natural
    (Scheme.ProEt.topology T) (condensedRingObj Λ T) i.hom
    (𝟙 (E.functor.obj (B₀ a T))) U y z
  have hp' : ((tensorRight (E.functor.obj (B₀ a T))).map i.hom).val.app U
      (ModuleRingedComparison.sectionPureTensor Λ T (E.functor.obj N)
        (E.functor.obj (B₀ a T)) U y z) =
      ModuleRingedComparison.sectionPureTensor Λ T M (E.functor.obj (B₀ a T)) U
        (i.hom.val.app U y) z := by
    change ((i.hom ▷ E.functor.obj (B₀ a T)).val.app U)
      (CategoryTheory.InternalAbelianSheafModule.comparison_sectionTmul
        (Scheme.ProEt.topology T) (condensedRingObj Λ T) (E.functor.obj N)
        (E.functor.obj (B₀ a T)) U y z) = _
    simpa only [tensorHom_id, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] using hp
  exact h.trans (hp'.trans (congrArg
    (fun x ↦ ModuleRingedComparison.sectionPureTensor Λ T M
      (E.functor.obj (B₀ a T)) U x z) hxy))

/-- The internal scalar and tensor normalizations transport to section modules.
Source: Stacks Tags 03EK, 06YY, 07A6; blueprint paragraph (1), steps 1--5.
(auxiliary; not a blueprint node).
Proof: conjugate the ordinary and derived internal comparisons by the fixed exact
section equivalences and their tensor comparison. The pure generator equation is
preserved by the balanced tensor formula and symmetry. On flat-term K-flat
representatives the universal computation equations cancel the scalar and tensor
counits; localization and essential surjectivity then give the displayed equation
for every derived object. -/
theorem section_tensor_normalized_of_normalized (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (s : SectionScalarComparison a T)
    (hs : SectionScalarNormalized a T s) (t : TensorNormalization a T)
    (ht : TensorNormalized a T t) : SectionTensorNormalized a T s t := by
  let o := ordinarySectionComparison a T s t
  let e := derivedSectionComparison a T s t
  have ho := ordinary_generator a T s hs t
  have he := derivedSectionComparison_conjugation a T s t
  refine ⟨o, ho, e, ?_, he⟩
  exact section_tensor_conjugate_computation a T s hs t ht o ho e he

end AlgebraicGeometry.ProEtale.QuotientChange
