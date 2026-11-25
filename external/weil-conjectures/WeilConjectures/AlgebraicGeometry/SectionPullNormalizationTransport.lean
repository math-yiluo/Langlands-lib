/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
import WeilConjectures.AlgebraicGeometry.SectionPullComputationOfRealization
import all WeilConjectures.CategoryTheory.InternalSectionScalarAdjunction

/-! # Transport of normalized scalar pullback comparisons

Source: Stacks Project, Tags 03EK, 0D6D, 07A6 and 0E47.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullback
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushforward
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedAdjunction
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushComparison

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

private theorem sectionEquivalence_map_apply
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (T : Scheme.{u}) {M N : Modules A T} (g : M ⟶ N) (W : T.ProEtᵒᵖ)
    (x : M.X.obj.obj W) :
    ((ModuleRingedComparison.equivalence A T).functor.map g).val.app W x =
      g.hom.hom.app W x := rfl

private theorem restriction_map_apply (φ : Λ ⟶ Λ') [IsMonHom φ] (T : Scheme.{u})
    {M N : ModuleRingedComparison.modules Λ' T} (g : M ⟶ N) (W : T.ProEtᵒᵖ)
    (x : M.val.obj W) :
    ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (coefficientMap φ T))).map g).val.app W x =
      g.val.app W x := rfl

private theorem pushforward_map_apply
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    {U V : Scheme.{u}} (h : U ⟶ V) {M N : ModuleRingedComparison.modules A U}
    (g : M ⟶ N) (W : V.ProEtᵒᵖ)
    (x : M.val.obj ((InternalModuleOperations.siteMap h).op.obj W)) :
    ((ModuleRingedComparison.pushforward A h).map g).val.app W x =
      g.val.app ((InternalModuleOperations.siteMap h).op.obj W) x := rfl

private theorem scalarRestrictionIso_hom_apply (φ : Λ ⟶ Λ') [IsMonHom φ]
    (T : Scheme.{u}) (M : Modules Λ' T) (W : T.ProEtᵒᵖ) (x : M.X.obj.obj W) :
    ((CategoryTheory.InternalAbelianSheafModule.scalarRestrictionIso
      (Scheme.ProEt.topology T) (coefficientMap φ T)).hom.app M).val.app W x = x := rfl

private theorem scalarRestrictionIso_inv_apply (φ : Λ ⟶ Λ') [IsMonHom φ]
    (T : Scheme.{u}) (M : Modules Λ' T) (W : T.ProEtᵒᵖ) (x : M.X.obj.obj W) :
    ((CategoryTheory.InternalAbelianSheafModule.scalarRestrictionIso
      (Scheme.ProEt.topology T) (coefficientMap φ T)).inv.app M).val.app W x = x := rfl

private theorem lowerComparison_inv_apply
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    {U V : Scheme.{u}} (h : U ⟶ V) (M : Modules A U) (W : V.ProEtᵒᵖ)
    (x : M.X.obj.obj ((InternalModuleOperations.siteMap h).op.obj W)) :
    ((InternalModuleOperations.lowerComparison A h).inv.app M).val.app W x = x := by
  have he := congrArg (fun t ↦ t.val.app W x)
    ((InternalModuleOperations.lowerComparison A h).inv_hom_id_app M)
  change ((InternalModuleOperations.lowerComparison A h).hom.app M).val.app W
    (((InternalModuleOperations.lowerComparison A h).inv.app M).val.app W x) = x at he
  rw [InternalModuleOperations.lowerComparison_apply] at he
  exact he

private theorem comapLowerStarIso_apply (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V) (M : Modules Λ' U) (W : V.ProEtᵒᵖ)
    (x : M.X.obj.obj ((InternalModuleOperations.siteMap h).op.obj W)) :
    ((CondensedRing.comapLowerStarIso φ h).hom.app M).hom.hom.app W x = x := by
  have he := Mod.comapMapModComapIso_hom_app_hom (h)_*[Ab.{u + 1}]
    (coefficientMap φ U) (coefficientMap φ V)
    (condensedPushforwardHom Λ h) (condensedPushforwardHom Λ' h)
    (condensedPushforwardHom_comp_map_coefficientMap φ h).symm M
  exact congrArg (fun t ↦ t.hom.app W x) he

private def sectionRestrictionPushImage (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (InternalModuleOperations.lowerComparison Λ' h).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CondensedRing.lowerStar Λ' h)
      (CategoryTheory.InternalAbelianSheafModule.scalarRestrictionIso
        (Scheme.ProEt.topology V) (coefficientMap φ V)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CondensedRing.comapLowerStarIso φ h)
      (ModuleRingedComparison.equivalence Λ V).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (V₀ φ U) (InternalModuleOperations.lowerComparison Λ h) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (CategoryTheory.InternalAbelianSheafModule.scalarRestrictionIso
        (Scheme.ProEt.topology U) (coefficientMap φ U)) _ ≪≫
    Functor.associator _ _ _

private def sectionRestrictionPush (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V) :
    ModuleRingedComparison.pushforward Λ' h ⋙
        SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology V) (coefficientMap φ V)) ≅
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology U) (coefficientMap φ U)) ⋙
        ModuleRingedComparison.pushforward Λ h :=
  ((Functor.whiskeringLeft _ _ _).obj
    (ModuleRingedComparison.equivalence Λ' U).functor).preimageIso
      (sectionRestrictionPushImage φ h)

-- The essential-image component calculation compares several nested section functors.
-- Its definitional equality checks exceed the default heartbeat count.
private theorem sectionRestrictionPush_apply (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (N : ModuleRingedComparison.modules Λ' U) (W : V.ProEtᵒᵖ)
    (x : ((ModuleRingedComparison.pushforward Λ' h).obj N).val.obj W) :
    ((sectionRestrictionPush φ h).hom.app N).val.app W x = x := by
  let E := ModuleRingedComparison.equivalence Λ' U
  have hi (M : Modules Λ' U) (z : M.X.obj.obj
      ((InternalModuleOperations.siteMap h).op.obj W)) :
      ((sectionRestrictionPush φ h).hom.app (E.functor.obj M)).val.app W z = z := by
    have heM := congrArg (fun t ↦ t.app M)
      (((Functor.whiskeringLeft _ _ _).obj E.functor).map_preimage
        (sectionRestrictionPushImage φ h).hom)
    change (sectionRestrictionPush φ h).hom.app (E.functor.obj M) = _ at heM
    rw [heM]
    simp only [sectionRestrictionPushImage, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      SheafOfModules.id_val, PresheafOfModules.id_app]
    erw [pushforward_map_apply Λ h, scalarRestrictionIso_hom_apply φ U,
      InternalModuleOperations.lowerComparison_apply Λ h, sectionEquivalence_map_apply Λ V,
      comapLowerStarIso_apply φ h, scalarRestrictionIso_inv_apply φ V,
      restriction_map_apply φ V, lowerComparison_inv_apply Λ' h]
    rfl
  have hn := (sectionRestrictionPush φ h).hom.naturality (E.counitIso.hom.app N)
  have hx := congrArg (fun t ↦ t.val.app W
    ((E.counitIso.inv.app N).val.app ((InternalModuleOperations.siteMap h).op.obj W) x)) hn
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hx
  have hiN := congrArg (fun t ↦ t.val.app
    ((InternalModuleOperations.siteMap h).op.obj W) x) (E.counitIso.inv_hom_id_app N)
  change (E.counitIso.hom.app N).val.app ((InternalModuleOperations.siteMap h).op.obj W)
    ((E.counitIso.inv.app N).val.app ((InternalModuleOperations.siteMap h).op.obj W) x) = x at hiN
  calc
    ((sectionRestrictionPush φ h).hom.app N).val.app W x =
        ((sectionRestrictionPush φ h).hom.app N).val.app W
          ((E.counitIso.hom.app N).val.app ((InternalModuleOperations.siteMap h).op.obj W)
            ((E.counitIso.inv.app N).val.app
              ((InternalModuleOperations.siteMap h).op.obj W) x)) :=
      congrArg _ hiN.symm
    _ = _ := hx
    _ = (E.counitIso.hom.app N).val.app ((InternalModuleOperations.siteMap h).op.obj W)
        ((E.counitIso.inv.app N).val.app
          ((InternalModuleOperations.siteMap h).op.obj W) x) :=
      congrArg _ (hi (E.inverse.obj N) _)
    _ = x := hiN

private def sectionOrdinaryPull (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V) :
    sV.pair.extension ⋙ ModuleRingedComparison.pullback Λ' h ≅
      ModuleRingedComparison.pullback Λ h ⋙ sU.pair.extension :=
  ((conjugateIsoEquiv
    (sV.pair.ordinaryAdjunction.comp (ModuleRingedComparison.adjunction Λ' h))
    ((ModuleRingedComparison.adjunction Λ h).comp sU.pair.ordinaryAdjunction)).symm
      (sectionRestrictionPush φ h)).symm

private theorem sectionOrdinaryPull_conjugate (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V) :
    conjugateEquiv
      (sV.pair.ordinaryAdjunction.comp (ModuleRingedComparison.adjunction Λ' h))
      ((ModuleRingedComparison.adjunction Λ h).comp sU.pair.ordinaryAdjunction)
      (sectionOrdinaryPull φ h sU sV).inv = (sectionRestrictionPush φ h).hom := by
  exact congrArg Iso.hom ((conjugateIsoEquiv
    (sV.pair.ordinaryAdjunction.comp (ModuleRingedComparison.adjunction Λ' h))
    ((ModuleRingedComparison.adjunction Λ h).comp sU.pair.ordinaryAdjunction)).apply_symm_apply
      (sectionRestrictionPush φ h))

private def sectionDerivedPull (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U) :
    sV.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' h ≅
      ModuleRingedComparison.derivedPullback Λ h ⋙ sU.pair.derived := by
  let e : (ModuleRingedComparison.derivedEquivalence Λ V).functor ⋙
        (sV.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' h) ≅
      (ModuleRingedComparison.derivedEquivalence Λ V).functor ⋙
        (ModuleRingedComparison.derivedPullback Λ h ⋙ sU.pair.derived) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight sV.derived.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (scalarSectionPullComparison Λ' h).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight b _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ sU.derived ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (scalarSectionPullComparison Λ h) _ ≪≫
      Functor.associator _ _ _
  exact ((Functor.whiskeringLeft _ _ _).obj
    (ModuleRingedComparison.derivedEquivalence Λ V).functor).preimageIso e

private theorem sectionDerivedPull_realization (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (M : DerivedCategory (Modules Λ V)) :
    (ModuleRingedComparison.derivedEquivalence Λ' U).functor.map (b.hom.app M) ≫
        sU.derived.hom.app ((L Λ h).obj M) ≫
        sU.pair.derived.map ((scalarSectionPullComparison Λ h).hom.app M) =
      (scalarSectionPullComparison Λ' h).hom.app ((D φ V).obj M) ≫
        (ModuleRingedComparison.derivedPullback Λ' h).map (sV.derived.hom.app M) ≫
        (sectionDerivedPull φ h sU sV b).hom.app
          ((ModuleRingedComparison.derivedEquivalence Λ V).functor.obj M) := by
  have he := congrArg (fun t ↦ t.app M)
    (((Functor.whiskeringLeft _ _ _).obj
      (ModuleRingedComparison.derivedEquivalence Λ V).functor).map_preimage
        (show (ModuleRingedComparison.derivedEquivalence Λ V).functor ⋙
            (sV.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' h) ⟶
          (ModuleRingedComparison.derivedEquivalence Λ V).functor ⋙
            (ModuleRingedComparison.derivedPullback Λ h ⋙ sU.pair.derived) from
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight sV.derived.symm _ ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (scalarSectionPullComparison Λ' h).symm ≪≫
            (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight b _ ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ sU.derived ≪≫
            (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (scalarSectionPullComparison Λ h) _ ≪≫
            Functor.associator _ _ _).hom))
  change (sectionDerivedPull φ h sU sV b).hom.app
      ((ModuleRingedComparison.derivedEquivalence Λ V).functor.obj M) = _ at he
  rw [he]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  erw [Category.id_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]

/-- A supplied universally normalized internal scalar/pullback comparison is
section-normalized with respect to any two normalized endpoint realizations.
Source: Stacks 03EK, 0D6D and 07A6; internal scalar/pullback normalization, step 8.
(auxiliary; not a blueprint node)

Proof: the identity restriction/direct-image map is conjugated by the endpoint
restriction comparisons to give the ordinary section square r. Both endpoint
restriction comparisons are identity on sections, so r is identity on sections.
Conjugate r under the specified composite ordinary scalar/geometric adjunctions
to obtain c. The normalized scalar units insert 1, so c is the ordinary balanced
pullback/scalar comparison. Use the K-flat scalar comparison theorem for these
endpoint scalar pairs and the specified ringed pullbacks to descend c to d.
The normalization equation for d is its K-flat computation equation. The two
endpoint scalar normalization equations and the geometric representative square
identify the realized b, after its computation maps, with d on each flat-term
K-flat representative: PullNormalized gives precisely the same ordinary balanced
map c. Cancel the invertible computation counits on such a representative.
For any unbounded object choose an incoming flat-term K-flat resolution. The
localized resolution is invertible, and naturality transports the comparison
equality from this representative to the object. These r, c and d together with
the displayed equality are exactly the witnesses of SectionPullNormalized.
There is no flatness condition on the coefficient map; zero coefficients,
identity geometric maps and empty schemes satisfy the same argument. -/
theorem section_pull_normalized_of_normalized (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (hU : SectionScalarNormalized φ U sU) (hV : SectionScalarNormalized φ V sV)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (normalized : PullNormalized φ h b) :
    SectionPullNormalized φ h sU sV b := by
  let r := sectionRestrictionPush φ h
  have hr := sectionRestrictionPush_apply φ h
  let c := sectionOrdinaryPull φ h sU sV
  have hc := sectionOrdinaryPull_conjugate φ h sU sV
  let d := sectionDerivedPull φ h sU sV b
  have hd := sectionDerivedPull_realization φ h sU sV b
  exact ⟨r, hr, c, hc, d,
    section_pull_computation_of_realization φ h sU sV hU hV b normalized r hr c hc d hd,
    hd⟩

end AlgebraicGeometry.ProEtale.QuotientChange
