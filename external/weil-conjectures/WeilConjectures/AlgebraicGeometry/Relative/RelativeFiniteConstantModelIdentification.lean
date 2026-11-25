/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility

/-! # Identification of the transported constant coefficient model

## References

* Stacks Project, Modules on Sites, Tag 03CY
* Stacks Project, Sites, Tag 03A0
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private def smallRestriction (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    SheafOfModules.{u + 1}
      (SheafOfModules.constantCoefficientRing (proEtaleModelTopology Y) B) ⥤
        Sheaf (proEtaleModelTopology Y) (ModuleCat.{u + 1} B) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars
      (SheafOfModules.constantCoefficientUnit (proEtaleModelTopology Y) B)).obj M.val
    let F : (proEtaleSiteModel Y)ᵒᵖ ⥤ ModuleCat.{u + 1} B :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by
          ext x
          exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp _ F
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := ⟨{
    app U := (ModuleCat.restrictScalars
      ((SheafOfModules.constantCoefficientUnit (proEtaleModelTopology Y) B).app U).hom).map
        (f.val.app U)
    naturality _ _ g := by
      ext x
      exact PresheafOfModules.naturality_apply f.val g x }⟩

private def smallRestrictionFullyFaithful (Y : Scheme.{u}) (B : Type (u + 1))
    [CommRing B] : (smallRestriction Y B).FullyFaithful where
  preimage {M N} f :=
    { val := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
        (SheafOfModules.constantCoefficientUnit (proEtaleModelTopology Y) B)
          N.isSheaf).symm
        { app := f.hom.app
          naturality g := by
            ext x
            exact ConcreteCategory.congr_hom (f.hom.naturality g) x } }
  map_preimage f := by ext U x; rfl
  preimage_map f := by ext U x; rfl

private def smallConstantComparisonHom (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (M : ModuleCat.{u + 1} B) :
    (constantSheaf (proEtaleModelTopology Y) (ModuleCat.{u + 1} B)).obj M ⟶
      (smallRestriction Y B).obj
        ((SheafOfModules.constantCoefficientModule (proEtaleModelTopology Y) B).obj M) := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (SheafOfModules.constantCoefficientUnit (proEtaleModelTopology Y) B)).unit.app
      ((SheafOfModules.strictPerfectConstantPresheaf (C := proEtaleSiteModel Y) B).obj M)
  exact ((sheafificationAdjunction (proEtaleModelTopology Y)
    (ModuleCat.{u + 1} B)).homEquiv _ _).symm
    { app := η.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (η.naturality f) x }

private theorem smallConstantComparisonHom_isIso (Y : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] (M : ModuleCat.{u + 1} B) :
    IsIso (smallConstantComparisonHom Y B M) := by
  let J := proEtaleModelTopology Y
  let N := (smallRestriction Y B).obj
    ((SheafOfModules.constantCoefficientModule J B).obj M)
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (SheafOfModules.constantCoefficientUnit J B)).unit.app
      ((SheafOfModules.strictPerfectConstantPresheaf (C := proEtaleSiteModel Y) B).obj M)
  let η' : (Functor.const (proEtaleSiteModel Y)ᵒᵖ).obj M ⟶ N.obj :=
    { app := η.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (η.naturality f) x }
  have hηi : Presheaf.IsLocallyInjective J η' := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem J
      (toSheafify J
        ((SheafOfModules.strictPerfectConstantPresheaf
          (C := proEtaleSiteModel Y) B).obj M).presheaf) x y h
  have hηs : Presheaf.IsLocallySurjective J η' := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem J
      (toSheafify J
        ((SheafOfModules.strictPerfectConstantPresheaf
          (C := proEtaleSiteModel Y) B).obj M).presheaf) x
  have hf : toSheafify J ((Functor.const (proEtaleSiteModel Y)ᵒᵖ).obj M) ≫
      (smallConstantComparisonHom Y B M).hom = η' :=
    ((sheafificationAdjunction J (ModuleCat.{u + 1} B)).homEquiv _ _).apply_symm_apply _
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · change Presheaf.IsLocallyInjective J (smallConstantComparisonHom Y B M).hom
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J η' hf
  · change Presheaf.IsLocallySurjective J (smallConstantComparisonHom Y B M).hom
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hf

private theorem smallConstantUnit (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    let e := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
    letI : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
      e.isEquivalence_inverse
    letI : e.inverse.IsDenseSubsite (proEtaleModelTopology Y) (ProEt.topology Y) := by
      change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
      infer_instance
    let c := (e.constantSheafSheafCongrIso (ProEt.topology Y)
      (proEtaleModelTopology Y) CommRingCat.{u + 1} terminalIsTerminal).app
        (CommRingCat.of B)
    Functor.whiskerLeft AsSmall.down.op
        (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of B))) ≫
      c.hom.hom =
        toSheafify (proEtaleModelTopology Y) ((Functor.const _).obj (CommRingCat.of B)) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
    infer_instance
  let hT : IsTerminal (⊤_ Y.ProEt) := terminalIsTerminal
  let a := ((constantSheafAdj (ProEt.topology Y) CommRingCat.{u + 1} hT).comp
    (e.sheafCongr (ProEt.topology Y) (proEtaleModelTopology Y)
      CommRingCat.{u + 1}).toAdjunction).ofNatIsoRight
    (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let b := constantSheafAdj (proEtaleModelTopology Y) CommRingCat.{u + 1}
    (hT.isTerminalObj e.functor)
  let f := (a.leftAdjointUniq b).hom.app (CommRingCat.of B)
  apply ((constantPresheafAdj CommRingCat.{u + 1}
    (hT.isTerminalObj e.functor)).homEquiv _ _).injective
  have h : a.unit.app (CommRingCat.of B) ≫
      ((sheafSections (proEtaleModelTopology Y) CommRingCat.{u + 1}).obj
        (op (e.functor.obj (⊤_ Y.ProEt)))).map f = b.unit.app (CommRingCat.of B) :=
    Adjunction.unit_leftAdjointUniq_hom_app a b (CommRingCat.of B)
  dsimp only [a] at h
  rw [Adjunction.ofNatIsoRight_unit] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
    Iso.refl_hom, Adjunction.comp_unit_app] at h
  dsimp only [constantSheafAdj] at h
  rw [Adjunction.comp_unit_app] at h
  simp only [constantPresheafAdj_unit_app, Category.id_comp] at h
  have hu : (e.sheafCongr (ProEt.topology Y) (proEtaleModelTopology Y)
      CommRingCat.{u + 1}).toAdjunction.unit.app
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj (CommRingCat.of B)) =
          𝟙 _ := by
    ext U x
    change (((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
      (CommRingCat.of B)).obj.map (𝟙 U)) x = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [hu] at h
  erw [CategoryTheory.Functor.map_id] at h
  simp only [Category.comp_id] at h
  dsimp only [b, constantSheafAdj] at h
  rw [Adjunction.comp_unit_app] at h
  simp only [constantPresheafAdj_unit_app, Category.id_comp,
    sheafificationAdjunction_unit_app] at h
  change (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of B))).app (op (⊤_ Y.ProEt)) ≫
      f.hom.app (op (e.functor.obj (⊤_ Y.ProEt))) =
        (toSheafify (proEtaleModelTopology Y)
          ((Functor.const _).obj (CommRingCat.of B))).app
            (op (e.functor.obj (⊤_ Y.ProEt))) at h
  simp only [Adjunction.homEquiv, constantPresheafAdj_unit_app, Equiv.coe_fn_mk,
    Category.id_comp]
  change (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of B))).app (op (⊤_ Y.ProEt)) ≫
      f.hom.app (op (e.functor.obj (⊤_ Y.ProEt))) =
        (toSheafify (proEtaleModelTopology Y)
          ((Functor.const _).obj (CommRingCat.of B))).app
            (op (e.functor.obj (⊤_ Y.ProEt)))
  exact h

private theorem transportUnit {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] (U : (proEtaleSiteModel Y)ᵒᵖ) (b : B) :
    ((relativeFiniteModelCoefficient g B).hom.hom.app U).hom
        ((SheafOfModules.constantCoefficientUnit (proEtaleModelTopology Y) B).app U b) =
      (relativeUnit g B).app (AsSmall.down.op.obj U) b := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
    infer_instance
  let c := (e.constantSheafSheafCongrIso (ProEt.topology Y)
    (proEtaleModelTopology Y) CommRingCat.{u + 1} terminalIsTerminal).app
      (CommRingCat.of B)
  have h : Functor.whiskerLeft AsSmall.down.op
      (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of B))) ≫
        c.hom.hom = toSheafify (proEtaleModelTopology Y)
          ((Functor.const _).obj (CommRingCat.of B)) := smallConstantUnit Y B
  have hi : toSheafify (proEtaleModelTopology Y)
      ((Functor.const _).obj (CommRingCat.of B)) ≫ c.inv.hom =
        Functor.whiskerLeft AsSmall.down.op
          (toSheafify (ProEt.topology Y)
            ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of B))) := by
    rw [← h, Category.assoc]
    change _ ≫ (c.hom ≫ c.inv).hom = _
    rw [c.hom_inv_id]
    exact Category.comp_id _
  have := relativeFiniteConstantInverseImage_isIso g B
  have hb := ConcreteCategory.congr_hom (congr_app hi U) b
  change (c.inv.hom.app U).hom
      ((toSheafify (proEtaleModelTopology Y)
        ((Functor.const _).obj (CommRingCat.of B))).app U b) = _ at hb
  simp only [relativeFiniteModelCoefficient, relativeUnit, constantCoefficients,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    CommRingCat.hom_comp, RingHom.comp_apply, SheafOfModules.constantCoefficientUnit]
  change ((inv (proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of B))).hom.app (AsSmall.down.op.obj U)).hom
        ((c.inv.hom.app U).hom
          ((toSheafify (proEtaleModelTopology Y)
            ((Functor.const _).obj (CommRingCat.of B))).app U b)) = _
  rw [hb]
  rfl

private def restrictionTransportIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B]
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) :
    (smallRestriction Y B).obj ((relativeFiniteModelModules g B).obj F) ≅
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
        (ModuleCat.{u + 1} B) (proEtaleModelTopology Y) (ProEt.topology Y)).obj
          ((relativeRestriction g B).obj F) := by
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ ?_) ?_)
  · refine (show (((smallRestriction Y B).obj
          ((relativeFiniteModelModules g B).obj F)).obj.obj U) ≃ₗ[B]
        (((relativeRestriction g B).obj F).obj.obj (AsSmall.down.op.obj U)) from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := ?_ }).toModuleIso
    intro b x
    exact congrArg (fun r ↦ r • (show F.val.obj (AsSmall.down.op.obj U) from x))
      (transportUnit g B U b)
  · intro U V f
    ext x
    rfl

/-- The explicit relative transport identifies the inverse-image constant module
with the constant coefficient module on every small-site slice, as module sheaves. -/
theorem relativeFiniteConstantModelIdentification {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B]
    (M : ModuleCat.{u + 1} B) (V : proEtaleSiteModel Y) :
    Nonempty (((relativeFiniteModelModules g B).obj
        ((proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj
          ((adicLisseConstantModules X B).obj M))).over V ≅
      ((SheafOfModules.constantCoefficientModule
        (proEtaleModelTopology Y) B).obj M).over V) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
    infer_instance
  let F := (proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj
    ((adicLisseConstantModules X B).obj M)
  let down := (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
    (ModuleCat.{u + 1} B) (proEtaleModelTopology Y) (ProEt.topology Y)
  have := smallConstantComparisonHom_isIso Y B M
  let t := restrictionTransportIso g B F ≪≫ down.mapIso (relativeConstant g B M) ≪≫
    (e.constantSheafSheafCongrIso (ProEt.topology Y) (proEtaleModelTopology Y)
      (ModuleCat.{u + 1} B) terminalIsTerminal).app M ≪≫
        asIso (smallConstantComparisonHom Y B M)
  let q := (smallRestrictionFullyFaithful Y B).preimageIso t
  exact ⟨(SheafOfModules.overFunctor _ V).mapIso q⟩

end AlgebraicGeometry.Scheme
