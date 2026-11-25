/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodedPresentation
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap

/-! # Normalized finite coefficient comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

private theorem encoding_smul (T : Scheme.{u}) (e : Encoding A T)
    (M : Internal A T) (V : T.ProEtᵒᵖ) (a : ULift.{u + 1} A)
    (m : M.X.obj.obj V) :
    a • (show ((sectionEncoding A T e.ringIso ⋙ fixedRestriction A T).obj M).obj.obj V from m) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (coefficient A) T) M.X).app V ≫
        (Mod.act (A := condensedRingObj (coefficient A) T) M.X).hom.app V).hom
        (((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
            (canonicalAbelianMap A T).hom).app V a) ⊗ₜ[ℤ] m) := by
  let J := Scheme.ProEt.topology T
  let B := ULift.{u + 1} A
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of B)
  have hc : Scheme.proEtaleModuleScalarUnit T A ≫ c.hom.hom =
      toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of B)) := by
    change _ ≫ ((constantCommuteCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
        (CommRingCat.of B)).hom = _
    erw [constantCommuteCompose_hom_app_hom]
    unfold Scheme.proEtaleModuleScalarUnit
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of B)
        (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)
  have hi : toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of B)) ≫ c.inv.hom =
      Scheme.proEtaleModuleScalarUnit T A := by
    rw [← hc, Category.assoc]
    change _ ≫ (c.hom ≫ c.inv).hom = _
    rw [Iso.hom_inv_id]
    exact Category.comp_id _
  change ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
      (condensedRingObj (coefficient A) T) M.X).app V ≫
      (Mod.act (A := condensedRingObj (coefficient A) T) M.X).hom.app V).hom
    (e.ringIso.hom.hom.app V (c.inv.hom.app V
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of B))).app V a)) ⊗ₜ[ℤ] m) = _
  erw [ConcreteCategory.congr_hom (congr_app hi V) a]
  apply congrArg (fun r ↦ ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
    (condensedRingObj (coefficient A) T) M.X).app V ≫
      (Mod.act (A := condensedRingObj (coefficient A) T) M.X).hom.app V).hom
        (r ⊗ₜ[ℤ] m))
  exact e.normalization V a

attribute [local instance] canonicalAbelianMap_isMonHom

private theorem scalar_monObj :
    (scalarSections.{u}).monObjObj (coefficient A) =
      AddCommGrpCat.ringMonObj (ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, A)) := by
  have he := scalarSections_monoidal_eq.{u}
  change @Functor.monObjObj _ _ _ _ _ _ scalarSections scalarSections_laxMonoidal _ _ = _
  rw [he]
  apply MonObj.ext
  let R := Profinite.continuousCoefficientRingSheaf A
  let : MonObj ((coefficient A).obj) := R.obj.monObjCompForget₂
  exact congr_app (Sheaf.μ_comp_map_mul (coefficient A))
    (Opposite.op (Profinite.of PUnit.{u + 1}))

private def scalarConstants :
    ULift.{u + 1} A ≃+* ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, A) where
  toFun x := ULift.up (ContinuousMap.const _ x.down)
  invFun f := ULift.up (f.down PUnit.unit)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    ext y
    exact congrArg f.down (Subsingleton.elim PUnit.unit y)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private def scalarHom :
    AddCommGrpCat.of (ULift.{u + 1} A) ⟶ scalarRingObj (coefficient A) :=
  (scalarConstants A).toAddEquiv.toAddCommGrpIso.hom

private instance scalarHom_isIso : IsIso (scalarHom A) := by
  unfold scalarHom
  infer_instance

private instance scalarHom_isMonHom : IsMonHom (scalarHom A) := by
  change @IsMonHom _ _ _ _ _ _ ((scalarSections.{u}).monObjObj _) _
  rw [scalar_monObj A]
  exact AddCommGrpCat.isMonHom_ofHom_ringHom (scalarConstants A).toRingHom

private def scalarEncoding :
    Mod Ab.{u + 1} (scalarRingObj (coefficient A)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} A) :=
  Mod.comap (scalarHom A) ⋙ internalToModule (ULift.{u + 1} A)

private instance scalarEncoding_equiv : (scalarEncoding A).IsEquivalence := by
  have : (Mod.comap (scalarHom A)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (scalarHom A)).isEquivalence_functor
  unfold scalarEncoding
  infer_instance

private instance scalarEncoding_additive : (scalarEncoding A).Additive := by
  have : (internalToModule (ULift.{u + 1} A)).Additive := ⟨by intros; rfl⟩
  unfold scalarEncoding
  infer_instance

private def scalarRegularCoordinates :
    (scalarEncoding A).obj (Mod.regular (scalarRingObj (coefficient A))) ≃ₗ[ULift.{u + 1} A]
      ULift.{u + 1} A :=
  ((internalToModule _).mapIso (Mod.regularIsoComapRegular (scalarHom A)).symm).toLinearEquiv.trans
    (internalRegularCoordinates _)

private def scalarFreeCoordinates (n : ℕ) :
    (scalarEncoding A).obj (Mod.finiteFree (scalarRingObj (coefficient A)) n) ≃ₗ[ULift.{u + 1} A]
      (Fin n → ULift.{u + 1} A) :=
  (((scalarEncoding A).mapBiproduct _).toLinearEquiv.trans
    (ModuleCat.biproductIsoPi _).toLinearEquiv).trans
      (LinearEquiv.piCongrRight fun _ ↦ scalarRegularCoordinates A)

private theorem scalar_fp_iff_finite [Finite A]
    (Q : Mod Ab.{u + 1} (scalarRingObj (coefficient A))) :
    Mod.IsFinitelyPresented (scalarRingObj (coefficient A)) Q ↔
      Finite ((scalarEncoding A).obj Q) := by
  classical
  let B := ULift.{u + 1} A
  let H := scalarEncoding A
  let R := scalarRingObj (coefficient A)
  constructor
  · rintro ⟨n, m, f, ⟨e⟩⟩
    have : Finite (H.obj (Mod.finiteFree R n)) :=
      Finite.of_equiv _ (scalarFreeCoordinates A n).toEquiv.symm
    have : Finite (cokernel (H.map f) : ModuleCat B) :=
      Finite.of_surjective (cokernel.π (H.map f))
        ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    exact Finite.of_equiv _
      (H.mapIso e ≪≫ PreservesCokernel.iso H f).toLinearEquiv.toEquiv.symm
  · intro h
    have := h
    have : Module.Finite B (H.obj Q) := Module.Finite.of_finite
    have : Module.FinitePresentation B (H.obj Q) :=
      Module.finitePresentation_of_finite B _
    obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' B (H.obj Q)
    let fn := (scalarFreeCoordinates A n).toModuleIso
    let fm := (scalarFreeCoordinates A m).toModuleIso
    let g' : H.obj (Mod.finiteFree R m) ⟶ H.obj (Mod.finiteFree R n) :=
      fm.hom ≫ ModuleCat.ofHom g ≫ fn.inv
    let f' : H.obj (Mod.finiteFree R n) ⟶ H.obj Q := fn.hom ≫ ModuleCat.ofHom f
    have hsurj : Function.Surjective f' := hf.comp fn.toLinearEquiv.surjective
    have hexact : Function.Exact g'.hom f'.hom := by
      intro x
      change f ((scalarFreeCoordinates A n) x) = 0 ↔ _
      rw [hg]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨(scalarFreeCoordinates A m).symm y, ?_⟩
        change (scalarFreeCoordinates A n).symm
          (g ((scalarFreeCoordinates A m) ((scalarFreeCoordinates A m).symm y))) = x
        rw [LinearEquiv.apply_symm_apply, hy, LinearEquiv.symm_apply_apply]
      · rintro ⟨y, hy⟩
        refine ⟨(scalarFreeCoordinates A m) y, ?_⟩
        change (scalarFreeCoordinates A n).symm
          (g ((scalarFreeCoordinates A m) y)) = x at hy
        exact ((scalarFreeCoordinates A n).symm_apply_eq).mp hy
    let gi := H.preimage g'
    have hgi : H.map gi = g' := H.map_preimage _
    let ci : H.obj Q ≅ cokernel g' :=
      (ModuleCat.isColimitCokernelCofork g' f' hexact hsurj).coconePointUniqueUpToIso
        (colimit.isColimit _)
    refine ⟨n, m, gi, ⟨H.preimageIso ?_⟩⟩
    exact ci ≪≫ cokernel.mapIso g' (H.map gi) (Iso.refl _) (Iso.refl _) (by simp [hgi]) ≪≫
      (PreservesCokernel.iso H gi).symm

private theorem pointScalar_counit :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map (scalarHom A) ≫
      (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
        Profinite.isTerminalPUnit).counit.app (coefficient A) =
    ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      _ (coefficient A)).symm (pointConstants A) := by
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  change (adj.homEquiv _ _).symm (scalarHom A) = _
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  dsimp only [adj, constantSheafAdj]
  rw [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, Equiv.apply_symm_apply]
  change scalarHom A = 𝟙 _ ≫ (pointConstants A).app
    (Opposite.op (Profinite.of PUnit.{u + 1}))
  rw [Category.id_comp]
  rfl

private theorem scalarCoefficient_normalization (T : Scheme.{u}) :
    (scalarConstant T).map (scalarHom A) ≫ scalarCoefficientHom (coefficient A) T =
      (constantSchemeIso T).inv.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫
        canonicalAbelianMap A T := by
  unfold scalarCoefficientHom scalarConstant canonicalAbelianMap
  rw [Functor.comp_map, ← Functor.map_comp, pointScalar_counit]
  simp

private instance scalarCoefficient_isIso [Finite A] [DiscreteTopology A] (T : Scheme.{u}) :
    IsIso (scalarCoefficientHom (coefficient A) T) := by
  have : IsIso (canonicalAbelianMap A T) := canonicalAbelianMap_isIso A T
  have h : IsIso ((scalarConstant T).map (scalarHom A) ≫
      scalarCoefficientHom (coefficient A) T) := by
    rw [scalarCoefficient_normalization A T]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp h

local instance :
    HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem scheme_monObj (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).monObjObj
        (AddCommGrpCat.of (ULift.{u + 1} A)) =
      Sheaf.monObj_presheafToSheaf_obj (Scheme.ProEt.topology T)
        (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A)) := by
  refine (Functor.monObjObj_comp _ _ _).trans ?_
  apply congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _
    (presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1}) _ _ m)
  apply MonObj.ext
  ext V
  rfl

private def constantBridge (T : Scheme.{u}) :
    @Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) _ _
      (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) _ _
      ((constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))
      ((constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).monObjObj
        (AddCommGrpCat.of (ULift.{u + 1} A))) ⥤
    @Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) _ _
      (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) _ _
      ((presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
        (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A)))
      (Sheaf.monObj_presheafToSheaf_obj (Scheme.ProEt.topology T)
        (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A))) := by
  let S := (presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
    (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A))
  let mC := (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).monObjObj
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let mS := Sheaf.monObj_presheafToSheaf_obj (Scheme.ProEt.topology T)
    (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A))
  have hid : @IsMonHom _ _ _ S S mC mC (𝟙 S) := by
    exact @IsMonHom.mk _ _ _ S S mC mC (𝟙 S) (by simp) (by simp)
  have hi : @IsMonHom _ _ _ S S mS mC (𝟙 S) :=
    IsMonHom.of_eq (𝟙 S) (scheme_monObj A T) rfl (hf := hid)
  exact @Mod.comap (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) _ _
    (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) _ _ S S mS mC (𝟙 S) hi

private theorem identityComap_action {C : Type*} [Category C] [MonoidalCategory C]
    (R : C) (mS mC : MonObj R) (hi : @IsMonHom C _ _ R R mS mC (𝟙 R))
    (M : @Mod C _ _ C _ _ R mC) :
    @Mod.act C _ _ R mS
      (@Mod.X C _ _ C _ _ R mS ((@Mod.comap C _ _ C _ _ R R mS mC (𝟙 R) hi).obj M))
      (@CategoryTheory.Mod.mod C _ _ C _ _ R mS
        ((@Mod.comap C _ _ C _ _ R R mS mC (𝟙 R) hi).obj M)) =
    @Mod.act C _ _ R mC (@Mod.X C _ _ C _ _ R mC M)
      (@CategoryTheory.Mod.mod C _ _ C _ _ R mC M) := by
  change 𝟙 R ▷ (@Mod.X C _ _ C _ _ R mC M) ≫
    @Mod.act C _ _ R mC (@Mod.X C _ _ C _ _ R mC M)
      (@CategoryTheory.Mod.mod C _ _ C _ _ R mC M) = _
  rw [id_whiskerRight, Category.id_comp]

private def constantInternalEncoding (T : Scheme.{u}) :=
  Mod.comap (canonicalAbelianMap A T) ⋙ constantBridge A T ⋙
    ConstantInternalModuleSheafEncoding.sheafEncoding (Scheme.ProEt.topology T)
      (ULift.{u + 1} A) (internalToModule (ULift.{u + 1} A)) rfl

private def encoding_constantInternal_iso (T : Scheme.{u}) (e : Encoding A T)
    (M : Internal A T) :
    (sectionEncoding A T e.ringIso ⋙ fixedRestriction A T).obj M ≅
      (constantInternalEncoding A T).obj M := by
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ ?_) ?_)
  · refine (show (((sectionEncoding A T e.ringIso ⋙ fixedRestriction A T).obj M).obj.obj U :
        Type (u + 1)) ≃ₗ[ULift.{u + 1} A] (((constantInternalEncoding A T).obj M).obj.obj U) from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a m ↦ ?_ }).toModuleIso
    refine (encoding_smul A T e M U a m).trans ?_
    symm
    change (((toSheafify (Scheme.ProEt.topology T)
      (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A))) ▷
        M.X.obj ≫ Functor.LaxMonoidal.μ
          (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          ((constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} A))) M.X ≫
        (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map
          ((𝟙 _) ▷ M.X ≫ (canonicalAbelianMap A T) ▷ M.X ≫ Mod.act M.X)).app U).hom
            (a ⊗ₜ[ℤ] m) = _
    simp only [id_whiskerRight, Category.id_comp, Functor.map_comp]
    erw [← Functor.LaxMonoidal.μ_natural_left_assoc]
    change (((toSheafify (Scheme.ProEt.topology T)
      (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A))) ▷
        M.X.obj ≫ (canonicalAbelianMap A T).hom ▷ M.X.obj ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (coefficient A) T) M.X) ≫
        (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map (Mod.act M.X)).app U).hom
          (a ⊗ₜ[ℤ] m) = _
    rw [← MonoidalCategory.comp_whiskerRight_assoc]
    change ((Functor.LaxMonoidal.μ
      (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (coefficient A) T) M.X).app U ≫
        (Mod.act M.X).hom.app U).hom
        (((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
            (canonicalAbelianMap A T).hom).app U ▷ M.X.obj.obj U).hom
              (a ⊗ₜ[ℤ] m)) = _
    rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul]
  · intro U V f
    ext m
    rfl

attribute [local irreducible] finiteConstantScalarExtension canonicalAbelianMap
  scalarCoefficientHom scalarHom

private instance constant_map_scalarHom (T : Scheme.{u}) :
    IsMonHom ((constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map (scalarHom A)) :=
  Functor.map.instIsMonHom _ _ (scalarHom A)

private instance scalar_map_scalarHom (T : Scheme.{u}) :
    IsMonHom ((scalarConstant T).map (scalarHom A)) :=
  Functor.map.instIsMonHom _ _ (scalarHom A)

private def scalarExtensionConstantIso [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (Q : Mod Ab.{u + 1} (scalarRingObj (coefficient A))) :
    (Mod.comap (canonicalAbelianMap A T)).obj
      ((finiteConstantScalarExtension (coefficient A) T).obj Q) ≅
      ((constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} A))).obj ((Mod.comap (scalarHom A)).obj Q) := by
  let F := scalarConstant T
  let G := constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}
  let h := scalarHom A
  let φ := scalarCoefficientHom (coefficient A) T
  let κ := canonicalAbelianMap A T
  let α : G ≅ F := constantSchemeIso T
  letI : IsMonHom κ := canonicalAbelianMap_isMonHom A T
  letI : IsMonHom φ := scalarCoefficientHom_isMonHom (coefficient A) T
  letI : IsMonHom (inv φ) := IsMonHom.inv φ
  letI : IsMonHom (F.map h) := scalar_map_scalarHom A T
  letI : IsMonHom (α.hom.app (AddCommGrpCat.of (ULift.{u + 1} A))) := by
    have hi := Functor.isMonHom_compAlgHom
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (upperStarFromPoint T) (constantSchemeIso T).inv
      (AddCommGrpCat.of (ULift.{u + 1} A))
    have hm : F.monObjObj (AddCommGrpCat.of (ULift.{u + 1} A)) =
        (upperStarFromPoint T).monObjObj
          ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} A))) :=
      Functor.monObjObj_comp _ _ _
    have hi' := IsMonHom.of_eq _ hm.symm rfl (hf := hi)
    exact monHomInvExplicit (F.monObjObj _) (G.monObjObj _) (α.app _).symm hi'
  letI : IsMonHom (κ ≫ inv φ) := by infer_instance
  letI : IsMonHom (α.hom.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫ F.map h) :=
    by infer_instance
  have hs : α.hom.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫ F.map h = κ ≫ inv φ := by
    apply (cancel_mono φ).mp
    rw [Category.assoc, scalarCoefficient_normalization A T]
    simp [κ, φ, α]
  let i := (Mod.extendScalarsIsoComapInv φ).app ((F.mapMod _).obj Q)
  unfold finiteConstantScalarExtension
  change (Mod.comap κ).obj ((Mod.extendScalars φ).obj ((F.mapMod _).obj Q)) ≅ _
  refine (Mod.comap κ).mapIso i ≪≫
    (Mod.comapComp κ (inv φ)).symm.app _ ≪≫
    (Mod.comapCongr hs.symm).app _ ≪≫
    (Mod.comapComp (α.hom.app _) (F.map h)).app _ ≪≫ ?_
  exact ((Mod.comap (α.hom.app _)).mapIso ((F.mapModComapIso h).app Q)).symm ≪≫
    ((Functor.mapModNatIso α (AddCommGrpCat.of (ULift.{u + 1} A))).app _).symm

private def constantPresheafModule (T : Scheme.{u})
    (N : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A))) :
    Mod (T.ProEtᵒᵖ ⥤ Ab.{u + 1})
      (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A)) where
  X := (Functor.const T.ProEtᵒᵖ).obj N.X
  mod := ModObj.mk' _
    { app := fun _ ↦ Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} A)) N.X
      naturality := fun _ ↦ by simp }
    (by
      apply NatTrans.ext
      funext V
      exact ModObj.one_smul_self (AddCommGrpCat.of (ULift.{u + 1} A)) N.X)
    (by
      apply NatTrans.ext
      funext V
      exact ModObj.mul_smul_self (AddCommGrpCat.of (ULift.{u + 1} A)) N.X)

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem constantPresheaf_action (T : Scheme.{u})
    (N : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A))) :
    Functor.LaxMonoidal.μ (Functor.const T.ProEtᵒᵖ)
        (AddCommGrpCat.of (ULift.{u + 1} A)) N.X ≫
      (Functor.const T.ProEtᵒᵖ).map (Mod.act N.X) =
    Mod.act (constantPresheafModule A T N).X := by
  ext V
  rfl

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem constantBridge_action (T : Scheme.{u})
    (N : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A))) :
    (Functor.LaxMonoidal.μ
      (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} A)) N.X ≫
      (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map (Mod.act N.X)) =
    (Functor.LaxMonoidal.μ (presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A))
      ((Functor.const T.ProEtᵒᵖ).obj N.X) ≫
      (presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map
        (Mod.act (constantPresheafModule A T N).X)) := by
  dsimp only [constantSheaf]
  erw [Functor.LaxMonoidal.comp_μ]
  rw [Category.assoc]
  dsimp only [Functor.comp_map]
  erw [← Functor.map_comp]
  exact congrArg (fun k ↦ Functor.LaxMonoidal.μ
    (presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A))
    ((Functor.const T.ProEtᵒᵖ).obj N.X) ≫
    (presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map k)
      (constantPresheaf_action A T N)

private theorem identity_intertwines {C : Type*} [Category C] [MonoidalCategory C]
    {R X : C} {g h : R ⊗ X ⟶ X} (e : g = h) :
    g ≫ 𝟙 X = R ◁ 𝟙 X ≫ h := by
  simpa only [Category.comp_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp] using e

private def identityComap_iso {C : Type*} [Category C] [MonoidalCategory C]
    (R : C) (mS mC : MonObj R) (hi : @IsMonHom C _ _ R R mS mC (𝟙 R))
    (M : @Mod C _ _ C _ _ R mC) (N : @Mod C _ _ C _ _ R mS)
    (i : @Mod.X C _ _ C _ _ R mC M ≅ @Mod.X C _ _ C _ _ R mS N)
    (h : @Mod.act C _ _ R mC (@Mod.X C _ _ C _ _ R mC M)
        (@CategoryTheory.Mod.mod C _ _ C _ _ R mC M) ≫ i.hom =
      R ◁ i.hom ≫ @Mod.act C _ _ R mS (@Mod.X C _ _ C _ _ R mS N)
        (@CategoryTheory.Mod.mod C _ _ C _ _ R mS N)) :
    ((@Mod.comap C _ _ C _ _ R R mS mC (𝟙 R) hi).obj M) ≅ N := by
  exact @Mod.isoMk C _ _ R mS
    ((@Mod.comap C _ _ C _ _ R R mS mC (𝟙 R) hi).obj M) N i
    ((congrArg (fun k ↦ k ≫ i.hom)
      (identityComap_action R mS mC hi M)).trans h)

private def constantBridgeSheafifyIso (T : Scheme.{u})
    (N : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A))) :
    (constantBridge A T).obj (((constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).mapMod
      (AddCommGrpCat.of (ULift.{u + 1} A))).obj N) ≅
    ((presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).mapMod
      (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A))).obj
      (constantPresheafModule A T N) := by
  let J := Scheme.ProEt.topology T
  let B := ULift.{u + 1} A
  let P := constantPresheafModule A T N
  refine identityComap_iso _ _ _ _ _ _ (Iso.refl _) ?_
  apply identity_intertwines
  exact (Functor.act_mapMod_obj (constantSheaf J Ab.{u + 1}) N).trans
    ((constantBridge_action A T N).trans
      (Functor.act_mapMod_obj (presheafToSheaf J Ab.{u + 1}) P).symm)

private def scalarConstantEncodedIso [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T)
    (Q : Mod Ab.{u + 1} (scalarRingObj (coefficient A))) :
    (e.ordinary.functor ⋙ e.fixed.functor).obj
      ((finiteConstantScalarExtension (coefficient A) T).obj Q) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj ((scalarEncoding A).obj Q) := by
  rw [e.ordinary_functor, e.fixed_functor]
  let J := Scheme.ProEt.topology T
  let B := ULift.{u + 1} A
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J B (internalToModule B) rfl
  let N := (Mod.comap (scalarHom A)).obj Q
  let P := constantPresheafModule A T N
  refine encoding_constantInternal_iso A T e _ ≪≫
    (constantBridge A T ⋙ H).mapIso (scalarExtensionConstantIso A T Q) ≪≫ ?_
  let i := constantBridgeSheafifyIso A T N
  exact H.mapIso i ≪≫
    (ConstantInternalModuleSheafEncoding.encSheafifyIso J B
      (internalToModule B) rfl).app P ≪≫
    (presheafToSheaf J (ModuleCat.{u + 1} B)).mapIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext m; rfl))

/-- Finite scalar models correspond to constant finite ordinary modules.
Source: Stacks Tag 099Y.
(auxiliary; not a blueprint node).

Proof: evaluation identifies continuous functions on the one-point profinite set with A.
The scalar module encoding preserves regular modules, finite free sums and cokernels.
Over a finite ring, finitely presented modules are finite; conversely finite modules are
finitely presented because finite rings are Noetherian. The scalar coefficient map is an
isomorphism: its composite with constant functions is the normalized coefficient map.
Thus extension along it is inverse scalar restriction. Monoidal constant-sheaf comparison
and module sheafification identify this model with the constant sheaf of the encoded scalar
module. Full faithfulness and essential surjectivity transport the model in both directions.
The argument includes the zero ring and empty schemes. -/
theorem finite_scalar_model_iff_constant [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) (M : Internal A T) :
    (∃ Q : Mod Ab.{u + 1} (scalarRingObj (coefficient A)),
      Mod.IsFinitelyPresented (scalarRingObj (coefficient A)) Q ∧
      Nonempty (M ≅ (finiteConstantScalarExtension (coefficient A) T).obj Q)) ↔
    ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A), Finite P ∧
      Nonempty ((e.ordinary.functor ⋙ e.fixed.functor).obj M ≅
        (constantSheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P) := by
  let H := e.ordinary.functor ⋙ e.fixed.functor
  constructor
  · rintro ⟨Q, hQ, ⟨i⟩⟩
    exact ⟨(scalarEncoding A).obj Q, (scalar_fp_iff_finite A Q).mp hQ,
      ⟨H.mapIso i ≪≫ scalarConstantEncodedIso A T e Q⟩⟩
  · rintro ⟨P, hP, ⟨i⟩⟩
    let Q := (scalarEncoding A).objPreimage P
    let j := (scalarEncoding A).objObjPreimageIso P
    have hQ : Finite ((scalarEncoding A).obj Q) :=
      Finite.of_equiv P j.toLinearEquiv.toEquiv.symm
    refine ⟨Q, (scalar_fp_iff_finite A Q).mpr hQ, ⟨H.preimageIso ?_⟩⟩
    exact i ≪≫ (constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))).mapIso j.symm ≪≫
        (scalarConstantEncodedIso A T e Q).symm

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
