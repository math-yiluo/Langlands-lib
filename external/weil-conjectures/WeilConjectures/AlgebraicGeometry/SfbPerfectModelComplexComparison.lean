/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfbCompletionRingComparison
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
import all WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Comparison of the completed coefficient complexes

Source: Bhatt--Scholze, Proposition 6.6.11, coefficient-model calculation;
Stacks Tags 03CY, 093J and 093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

attribute [-instance] AlgebraicGeometry.Scheme.torsionCompletionSheafify

open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

private instance (priority := 10000) modelComparisonWEquals (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} _

private instance (priority := 10000) modelComparisonHasSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  exact hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _

attribute [-instance] SheafOfModules.instAbelian in
private theorem modelCoefficientMap (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (sfbModelRings X).map (CompletedConstantReduction.base X I) ≫
        (sfbModelCompletionIso X I).hom =
      (sfbModelConstantsIso X).hom.app (CommRingCat.of A) ≫
        ConstantCompletion.coefficientMap (coefficientProEtaleModelTopology.{u, 0} X) A I := by
  apply limit.hom_ext
  intro n
  change _ ≫ ConstantCompletion.projection _ A I n.unop = _ ≫
    ConstantCompletion.projection _ A I n.unop
  rw [Category.assoc, sfbModelCompletionIso_projection, ← Category.assoc,
    ← Functor.map_comp]
  have hb : CompletedConstantReduction.base X I ≫
      limit.π (adicLisseRingSystem X I) (op n.unop) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1)))) :=
    (CompletedConstantReduction.base_exists X I).choose_spec.1 n.unop
  rw [hb]
  rw [Category.assoc]
  change _ = _ ≫ (ConstantCompletion.coefficientMap _ A I ≫
    limit.π (ConstantCompletion.finiteSystem _ A I) n)
  rw [ConstantCompletion.coefficientMap, limit.lift_π]
  exact (sfbModelConstantsIso X).hom.naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1))))

private abbrev modelRing (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :=
  ((AsSmall.down : coefficientProEtaleSiteModel.{u, 0} X ⥤
    X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientProEtaleModelTopology.{u, 0} X) (ProEt.topology X)).obj R

section Sheafification

variable (X : Scheme.{u})
  {R₀ : X.ProEtᵒᵖ ⥤ RingCat.{u + 1}}
  {R : Sheaf (ProEt.topology X) RingCat.{u + 1}}
  (η : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective (ProEt.topology X) η]
  [Presheaf.IsLocallySurjective (ProEt.topology X) η]

private abbrev modelUnit :=
  Functor.whiskerLeft (AsSmall.down : coefficientProEtaleSiteModel.{u, 0} X ⥤ X.ProEt).op η

attribute [-instance] SheafOfModules.instAbelian in
private instance modelUnit_injective :
    Presheaf.IsLocallyInjective (coefficientProEtaleModelTopology.{u, 0} X) (modelUnit X η) :=
  Presheaf.isLocallyInjective_whisker
    (coefficientProEtaleModelTopology.{u, 0} X) (ProEt.topology X) AsSmall.down η

attribute [-instance] SheafOfModules.instAbelian in
private instance modelUnit_surjective :
    Presheaf.IsLocallySurjective (coefficientProEtaleModelTopology.{u, 0} X) (modelUnit X η) :=
  Presheaf.isLocallySurjective_whisker
    (coefficientProEtaleModelTopology.{u, 0} X) (ProEt.topology X) AsSmall.down η

attribute [-instance] SheafOfModules.instAbelian in
private def modelSheafificationSeed (M : _root_.PresheafOfModules.{u + 1} R₀) :
    (_root_.PresheafOfModules.pushforward₀.{u + 1} AsSmall.down R₀).obj M ⟶
      (_root_.PresheafOfModules.restrictScalars.{u + 1} (modelUnit X η)).obj
        ((proEtaleModuleToModel.{u} (X := X) R).obj ((_root_.PresheafOfModules.sheafification.{u +
            1} (J := ProEt.topology X) (R := R) η).obj
            M)).val where
  app U := (_root_.PresheafOfModules.sheafificationAdjunction.{u + 1} (J := ProEt.topology X) (R
      := R) η).unit.app M |>.app
    (AsSmall.down.op.obj U)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact _root_.PresheafOfModules.naturality_apply
      ((_root_.PresheafOfModules.sheafificationAdjunction.{u + 1} (J := ProEt.topology X) (R := R)
          η).unit.app M)
      (AsSmall.down.op.map f) x

attribute [-instance] SheafOfModules.instAbelian in
private def modelSheafificationComparison (M : _root_.PresheafOfModules.{u + 1} R₀) :
    (_root_.PresheafOfModules.sheafification.{u + 1} (J := coefficientProEtaleModelTopology.{u, 0}
        X)
      (R := modelRing X R) (modelUnit X η)).obj
        ((_root_.PresheafOfModules.pushforward₀.{u + 1} AsSmall.down R₀).obj M) ⟶
      (proEtaleModuleToModel.{u} (X := X) R).obj ((_root_.PresheafOfModules.sheafification.{u + 1}
          (J := ProEt.topology X) (R := R) η).obj M) :=
  (_root_.PresheafOfModules.sheafificationHomEquiv.{u + 1} (J :=
      coefficientProEtaleModelTopology.{u, 0} X)
      (R := modelRing X R) (modelUnit X
      η)).symm
    (modelSheafificationSeed X η M)

attribute [-instance] SheafOfModules.instAbelian in
private theorem modelSheafificationComparison_underlying (M : _root_.PresheafOfModules.{u + 1} R₀) :
    (SheafOfModules.toSheaf.{u + 1} (modelRing X R)).map (modelSheafificationComparison X η M) =
      (((AsSmall.down : coefficientProEtaleSiteModel.{u, 0} X ⥤
        X.ProEt).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
          (coefficientProEtaleModelTopology.{u, 0} X) (ProEt.topology X)).hom.app
            M.presheaf) := by
  unfold modelSheafificationComparison
  rw [_root_.PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((sheafificationAdjunction (coefficientProEtaleModelTopology.{u, 0} X)
    AddCommGrpCat.{u + 1}).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact ((AsSmall.down : coefficientProEtaleSiteModel.{u, 0} X ⥤
      X.ProEt).toSheafify_pullbackSheafificationCompatibility AddCommGrpCat.{u + 1}
      (coefficientProEtaleModelTopology.{u, 0} X) (ProEt.topology X) M.presheaf).symm

attribute [-instance] SheafOfModules.instAbelian in
private instance modelSheafificationComparison_isIso (M : _root_.PresheafOfModules.{u + 1} R₀) :
    IsIso (modelSheafificationComparison X η M) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{u + 1} (modelRing X R)),
    modelSheafificationComparison_underlying]
  infer_instance

attribute [local irreducible] modelSheafificationComparison modelSheafificationSeed

attribute [-instance] SheafOfModules.instAbelian in
private def modelSheafificationIso :
    _root_.PresheafOfModules.pushforward₀.{u + 1} AsSmall.down R₀ ⋙
        _root_.PresheafOfModules.sheafification.{u + 1} (J := coefficientProEtaleModelTopology.{u,
            0} X)
      (R := modelRing X R) (modelUnit X η) ≅
      _root_.PresheafOfModules.sheafification.{u + 1} (J := ProEt.topology X) (R := R) η ⋙
          proEtaleModuleToModel.{u} (X :=
          X) R := by
  refine NatIso.ofComponents (fun M ↦ asIso (modelSheafificationComparison X η M)) ?_
  intro M N f
  apply (SheafOfModules.toSheaf.{u + 1} (modelRing X R)).map_injective
  simp only [Functor.map_comp, asIso_hom, modelSheafificationComparison_underlying]
  exact (((AsSmall.down : coefficientProEtaleSiteModel.{u, 0} X ⥤
        X.ProEt).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
      (coefficientProEtaleModelTopology.{u, 0} X) (ProEt.topology X)).hom.naturality
        ((_root_.PresheafOfModules.toPresheaf.{u + 1} R₀).map f))

attribute [local irreducible] modelSheafificationIso

end Sheafification

attribute [-instance] SheafOfModules.instAbelian in
private theorem modelConstants_unitComm (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Functor.whiskerLeft
        (AsSmall.down : coefficientProEtaleSiteModel.{u, 0} X ⥤ X.ProEt).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))) ≫
      ((sfbModelConstantsIso X).hom.app (CommRingCat.of A)).hom =
    toSheafify (coefficientProEtaleModelTopology.{u, 0} X)
      ((Functor.const (coefficientProEtaleSiteModel.{u, 0} X)ᵒᵖ).obj (CommRingCat.of A)) := by
  let e := ((AsSmall.down : coefficientProEtaleSiteModel.{u, 0} X ⥤
        X.ProEt).pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
      (coefficientProEtaleModelTopology.{u, 0} X) (ProEt.topology X)).app
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))
  have h := (AsSmall.down : coefficientProEtaleSiteModel.{u, 0} X ⥤
      X.ProEt).toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
      (coefficientProEtaleModelTopology.{u, 0} X) (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))
  change _ ≫ e.inv.hom = _
  rw [← h, Category.assoc]
  change _ ≫ (e.hom ≫ e.inv).hom = _
  rw [e.hom_inv_id]
  exact Category.comp_id _

attribute [local irreducible] sfbModelConstantsIso sfbModelCompletionIso
attribute [local irreducible] moduleSheafificationComparison moduleSheafificationSeed

attribute [-instance] SheafOfModules.instAbelian in
private theorem modelConstants_unit (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    modelUnit X (R := adicLisseRing X A) (adicLisseConstantUnit X A) ≫
      ((sheafCompose (coefficientProEtaleModelTopology.{u, 0} X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((sfbModelConstantsIso X).hom.app (CommRingCat.of A))).hom =
      realizationRingUnit (coefficientProEtaleModelTopology.{u, 0} X) A := by
  exact congrArg (fun t ↦ Functor.whiskerRight t
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) (modelConstants_unitComm X A)

private abbrev actualConstantPresheaf (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    _root_.PresheafOfModules.pushforward₀.{u + 1}
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))

attribute [-instance] SheafOfModules.instAbelian in
private def modelConstantPresheafIso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    actualConstantPresheaf X A ⋙
        _root_.PresheafOfModules.pushforward₀.{u + 1} AsSmall.down
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A)) ≅
      siteConstantModulePresheafGeneral (C := coefficientProEtaleSiteModel.{u, 0} X) A :=
  NatIso.ofComponents (fun M ↦ _root_.PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)
    (by intros; rfl)) (by intros; rfl)

attribute [local irreducible] modelConstantPresheafIso

private def liftNaturalIso
    {D E B : Type*} [Category D] [Category E] [Category B]
    {F G : D ⥤ E} (T : E ⥤ B) [T.Faithful] (e : F ⋙ T ≅ G ⋙ T)
    (c : ∀ M, F.obj M ≅ G.obj M)
    (hc : ∀ M, T.map (c M).hom = e.hom.app M) : F ≅ G :=
  NatIso.ofComponents c (by
    intro M N f
    apply T.map_injective
    rw [T.map_comp, T.map_comp, hc, hc]
    exact e.hom.naturality f)

attribute [local irreducible] liftNaturalIso

section ModuleRingTransport

variable {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  {R₀ : Cᵒᵖ ⥤ RingCat.{u + 1}} {R S : Sheaf J RingCat.{u + 1}}
  (ηR : R₀ ⟶ R.obj) (ηS : R₀ ⟶ S.obj)
  [Presheaf.IsLocallyInjective J ηR] [Presheaf.IsLocallySurjective J ηR]
  [Presheaf.IsLocallyInjective J ηS] [Presheaf.IsLocallySurjective J ηS]
  (α : R ⟶ S) (hsq : ηR ≫ α.hom = ηS)

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
attribute [-instance] SheafOfModules.instAbelian in
private def moduleRestrictionCompToSheaf :
    SheafOfModules.restrictScalars α ⋙ SheafOfModules.toSheaf.{u + 1} R ≅
      SheafOfModules.toSheaf.{u + 1} S := Iso.refl _

attribute [local instance] moduleSheafificationComparison_isIso

attribute [-instance] SheafOfModules.instAbelian in
private def moduleRingTransport :
    _root_.PresheafOfModules.sheafification.{u + 1} ηR ≅
      _root_.PresheafOfModules.sheafification.{u + 1} ηS ⋙
        SheafOfModules.restrictScalars α := by
  let e := _root_.PresheafOfModules.sheafificationCompToSheaf.{u + 1} ηR ≪≫
    (_root_.PresheafOfModules.sheafificationCompToSheaf.{u + 1} ηS).symm ≪≫
    (isoWhiskerLeft (_root_.PresheafOfModules.sheafification.{u + 1} ηS)
      (moduleRestrictionCompToSheaf J α)).symm
  refine liftNaturalIso (SheafOfModules.toSheaf.{u + 1} R) e
    (fun M ↦ asIso (moduleSheafificationComparison J ηR ηS α hsq M)) ?_
  intro M
  simp only [asIso_hom, e, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    isoWhiskerLeft_inv, whiskerLeft_app, _root_.PresheafOfModules.sheafificationCompToSheaf,
    moduleRestrictionCompToSheaf, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.comp_obj]
  change (SheafOfModules.toSheaf.{u + 1} R).map
      (moduleSheafificationComparison J ηR ηS α hsq M) =
    𝟙 ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj M.presheaf) ≫
      𝟙 ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj M.presheaf)
  exact (moduleSheafificationComparison_toSheaf J ηR ηS α hsq M).trans
    (Category.id_comp _).symm

attribute [local irreducible] moduleRingTransport

end ModuleRingTransport

attribute [-instance] SheafOfModules.instAbelian in
private def modelConstantRingTransport (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    siteConstantModulePresheafGeneral (C := coefficientProEtaleSiteModel.{u, 0} X) A ⋙
        _root_.PresheafOfModules.sheafification.{u + 1}
          (R := modelRing X (adicLisseRing X A)) (modelUnit X (R := adicLisseRing X A)
              (adicLisseConstantUnit X A)) ≅
      commutativeSiteConstantModuleFunctor (coefficientProEtaleModelTopology.{u, 0} X) A ⋙
        ConstantCompletion.res ((sfbModelConstantsIso X).hom.app (CommRingCat.of A)) := by
  let J := coefficientProEtaleModelTopology.{u, 0} X
  let ηA : (Functor.const (coefficientProEtaleSiteModel.{u, 0} X)ᵒᵖ).obj (RingCat.of A) ⟶
      (modelRing X (adicLisseRing X A)).obj :=
    modelUnit X (R := adicLisseRing X A) (adicLisseConstantUnit X A)
  let B := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (realizationRing J A)
  let ηB := realizationRingUnit J A
  letI := (realizationRingUnit_locallyBijective J A).1
  letI := (realizationRingUnit_locallyBijective J A).2
  let α : modelRing X (adicLisseRing X A) ⟶ B :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    ((sfbModelConstantsIso X).hom.app (CommRingCat.of A))
  have h : ηA ≫ α.hom = ηB := modelConstants_unit X A
  let Q := siteConstantModulePresheafGeneral (C := coefficientProEtaleSiteModel.{u, 0} X) A
  change (Q ⋙ _root_.PresheafOfModules.sheafification.{u + 1} (J := J) (R := modelRing X
      (adicLisseRing X A)) ηA) ≅
    Q ⋙ _root_.PresheafOfModules.sheafification.{u + 1} (J := J) (R := B) ηB ⋙
        SheafOfModules.restrictScalars α
  exact isoWhiskerLeft Q (moduleRingTransport J ηA ηB α h)

attribute [local irreducible] modelConstantRingTransport

attribute [-instance] SheafOfModules.instAbelian in
private def modelConstantModulesIso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    adicLisseConstantModules X A ⋙ proEtaleModuleToModel.{u} (X := X) (adicLisseRing X A) ≅
      commutativeSiteConstantModuleFunctor (coefficientProEtaleModelTopology.{u, 0} X) A ⋙
        ConstantCompletion.res ((sfbModelConstantsIso X).hom.app (CommRingCat.of A)) :=
  isoWhiskerLeft (actualConstantPresheaf X A)
      (modelSheafificationIso X (R := adicLisseRing X A) (adicLisseConstantUnit X A)).symm ≪≫
    isoWhiskerRight (modelConstantPresheafIso X A)
      (_root_.PresheafOfModules.sheafification.{u + 1}
        (R := modelRing X (adicLisseRing X A)) (modelUnit X (R := adicLisseRing X A)
            (adicLisseConstantUnit X A))) ≪≫
    modelConstantRingTransport X A

attribute [local irreducible] modelConstantModulesIso

section ScalarExtension

variable (X : Scheme.{u})
  {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)

attribute [-instance] SheafOfModules.instAbelian in
private def actualScalarPresheaf (φ : R ⟶ S) :
    proEtaleRingModules X R ⥤ _root_.PresheafOfModules.{u + 1} ((adicLisseForget X).obj S).obj where
  obj := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
    (J := ProEt.topology X) (R₁ := R) (R₂ := S) φ
  map f :=
    { app := fun U ↦ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (φ.hom.app U).hom).map
        (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality.{u, u + 1, u + 1}
        (J := ProEt.topology X) (R₁ := R) (R₂ := S) φ _ f }
  map_id M := by
    apply _root_.PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (φ.hom.app U).hom).map_id _
  map_comp f g := by
    apply _root_.PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (φ.hom.app U).hom).map_comp _ _

attribute [-instance] SheafOfModules.instAbelian in
private theorem actualScalar_obj (M : proEtaleRingModules X R) :
    (completedAdicChange X φ).obj M =
      ((_root_.PresheafOfModules.sheafification.{u + 1} (J := ProEt.topology X)
        (R := (adicLisseForget X).obj S) (𝟙 ((adicLisseForget X).obj S).obj)).obj
          ((actualScalarPresheaf X φ).obj M)) :=
  (completedAdicChangeData X φ).choose_spec.choose M

attribute [-instance] SheafOfModules.instAbelian in
private theorem actualScalar_map {M N : proEtaleRingModules X R} (f : M ⟶ N) :
    (completedAdicChange X φ).map f =
      eqToHom (actualScalar_obj X φ M) ≫
        ((_root_.PresheafOfModules.sheafification.{u + 1} (J := ProEt.topology X)
          (R := (adicLisseForget X).obj S) (𝟙 ((adicLisseForget X).obj S).obj)).map
            ((actualScalarPresheaf X φ).map f)) ≫
          eqToHom (actualScalar_obj X φ N).symm :=
  (completedAdicChangeData X φ).choose_spec.choose_spec.choose f

attribute [-instance] SheafOfModules.instAbelian in
private def actualScalarIso :
    completedAdicChange X φ ≅ actualScalarPresheaf X φ ⋙
      _root_.PresheafOfModules.sheafification.{u + 1} (J := ProEt.topology X)
        (R := (adicLisseForget X).obj S) (𝟙 ((adicLisseForget X).obj S).obj) := by
  refine NatIso.ofComponents (fun M ↦ eqToIso (actualScalar_obj X φ M)) ?_
  intro M N f
  dsimp only [eqToIso.hom]
  rw [actualScalar_map]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, Functor.comp_map]

attribute [local irreducible] actualScalarIso

attribute [-instance] SheafOfModules.instAbelian in
private def modelScalarPresheafIso :
    actualScalarPresheaf X φ ⋙
        _root_.PresheafOfModules.pushforward₀.{u + 1} AsSmall.down ((adicLisseForget X).obj S).obj ≅
      proEtaleModuleToModel.{u} (X := X) ((adicLisseForget X).obj R) ⋙
        SheafOfModules.RingedTensor.tensorPresheafFunctor ((sfbModelRings X).map φ) := by
  refine NatIso.ofComponents (fun M ↦ _root_.PresheafOfModules.isoMk
    (fun U ↦ (LinearEquiv.refl _ _).toModuleIso) ?_) ?_
  · intro U V f
    apply ModuleCat.ExtendScalars.hom_ext
      (R := R.obj.obj (AsSmall.down.op.obj U)) (S := S.obj.obj (AsSmall.down.op.obj U))
    intro x
    change SheafOfModules.changeOfRingsMap φ M (AsSmall.down.op.map f)
      ((1 : S.obj.obj (AsSmall.down.op.obj U)) ⊗ₜ[R.obj.obj (AsSmall.down.op.obj U),
        (φ.hom.app (AsSmall.down.op.obj U)).hom] x) =
      SheafOfModules.changeOfRingsMap ((sfbModelRings X).map φ)
        ((proEtaleModuleToModel.{u} (X := X) ((adicLisseForget X).obj R)).obj M) f _
    exact (SheafOfModules.changeOfRingsMap_tmul.{u, u + 1, u + 1}
      φ M (AsSmall.down.op.map f) (1 : S.obj.obj (AsSmall.down.op.obj U)) x).trans
      (SheafOfModules.changeOfRingsMap_tmul.{u + 1, u + 1, u + 1}
        ((sfbModelRings X).map φ)
        ((proEtaleModuleToModel.{u} (X := X) ((adicLisseForget X).obj R)).obj M)
        f (1 : S.obj.obj (AsSmall.down.op.obj U)) x).symm
  · intro M N f
    apply _root_.PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.ExtendScalars.hom_ext
      (R := R.obj.obj (AsSmall.down.op.obj U)) (S := S.obj.obj (AsSmall.down.op.obj U))
    intro x
    rfl

attribute [local irreducible] modelScalarPresheafIso

attribute [-instance] SheafOfModules.instAbelian modelUnit_injective modelUnit_surjective in
private def modelScalarChangeIso :
    completedAdicChange X φ ⋙ proEtaleModuleToModel.{u} (X := X) ((adicLisseForget X).obj S) ≅
      proEtaleModuleToModel.{u} (X := X) ((adicLisseForget X).obj R) ⋙
        ConstantCompletion.change ((sfbModelRings X).map φ) := by
  let J := coefficientProEtaleModelTopology.{u, 0} X
  let T := modelRing X ((adicLisseForget X).obj S)
  letI : Presheaf.IsLocallyInjective J (𝟙 T.obj) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ _ _ h ↦ h)
  letI : Presheaf.IsLocallySurjective J (𝟙 T.obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ x ↦ ⟨x, rfl⟩)
  exact isoWhiskerRight (actualScalarIso X φ) (proEtaleModuleToModel.{u} (X := X) ((adicLisseForget
      X).obj S)) ≪≫
    isoWhiskerLeft (actualScalarPresheaf X φ)
      (modelSheafificationIso X (R := (adicLisseForget X).obj S)
        (𝟙 ((adicLisseForget X).obj S).obj)).symm ≪≫
    isoWhiskerRight (modelScalarPresheafIso X φ)
      (_root_.PresheafOfModules.sheafification.{u + 1}
        (J := coefficientProEtaleModelTopology.{u, 0} X)
        (R := modelRing X ((adicLisseForget X).obj S))
        (𝟙 (modelRing X ((adicLisseForget X).obj S)).obj))

attribute [local irreducible] modelScalarChangeIso

end ScalarExtension

section ScalarIsomorphisms

variable {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}

attribute [-instance] SheafOfModules.instAbelian in
private def scalarRestrictionIdIso (R : Sheaf J CommRingCat.{u + 1}) :
    ConstantCompletion.res (𝟙 R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (_root_.PresheafOfModules.isoMk (fun _ ↦ Iso.refl _))) (by intros; rfl)

attribute [-instance] SheafOfModules.instAbelian in
private def scalarRestrictionEquivalence {R S : Sheaf J CommRingCat.{u + 1}} (e : R ≅ S) :
    ConstantCompletion.Mod S ≌ ConstantCompletion.Mod R := by
  let a : ConstantCompletion.res e.hom ⋙ ConstantCompletion.res e.inv ≅ 𝟭 _ :=
    AdicPerfectModel.scalarRestrictionComp e.inv e.hom ≪≫
      eqToIso (congrArg (fun f ↦ ConstantCompletion.res f) e.inv_hom_id) ≪≫
      scalarRestrictionIdIso S
  let b : ConstantCompletion.res e.inv ⋙ ConstantCompletion.res e.hom ≅ 𝟭 _ :=
    AdicPerfectModel.scalarRestrictionComp e.hom e.inv ≪≫
      eqToIso (congrArg (fun f ↦ ConstantCompletion.res f) e.hom_inv_id) ≪≫
      scalarRestrictionIdIso R
  exact CategoryTheory.Equivalence.mk
    (ConstantCompletion.res e.hom) (ConstantCompletion.res e.inv) a.symm b

attribute [-instance] SheafOfModules.instAbelian in
private def scalarChangeIso {R S : Sheaf J CommRingCat.{u + 1}} (e : R ≅ S) :
    ConstantCompletion.change e.inv ≅ ConstantCompletion.res e.hom :=
  Adjunction.leftAdjointUniq (AdicPerfectModel.scalarAdjunction e.inv)
    (scalarRestrictionEquivalence e).toAdjunction

attribute [-instance] SheafOfModules.instAbelian in
private def scalarChangeSquare
    {R R' S S' : Sheaf J CommRingCat.{u + 1}} (eR : R ≅ R') (eS : S ≅ S')
    (φ : R ⟶ S) (ψ : R' ⟶ S') (hsq : φ ≫ eS.hom = eR.hom ≫ ψ) :
    ConstantCompletion.res eR.hom ⋙ ConstantCompletion.change φ ≅
      ConstantCompletion.change ψ ⋙ ConstantCompletion.res eS.hom := by
  have h : eR.inv ≫ φ = ψ ≫ eS.inv := by
    apply (cancel_mono eS.hom).mp
    simp only [Category.assoc, hsq, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
  exact isoWhiskerRight (scalarChangeIso eR).symm (ConstantCompletion.change φ) ≪≫
    AdicPerfectModel.scalarChangeComp eR.inv φ ≪≫
    eqToIso (congrArg (fun f ↦ ConstantCompletion.change f) h) ≪≫
    (AdicPerfectModel.scalarChangeComp ψ eS.inv).symm ≪≫
    isoWhiskerLeft (ConstantCompletion.change ψ) (scalarChangeIso eS)

end ScalarIsomorphisms

attribute [-instance] SheafOfModules.instAbelian in
private def completedRealizationIso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (I : Ideal A) :
    adicLisseConstantModules X A ⋙ completedAdicChange X (CompletedConstantReduction.base X I) ⋙
        proEtaleModuleToModel.{u} (X := X) ((adicLisseForget X).obj (adicLisseCompletedRing X I)) ≅
      commutativeSiteConstantModuleFunctor (coefficientProEtaleModelTopology.{u, 0} X) A ⋙
        ConstantCompletion.change
          (ConstantCompletion.coefficientMap (coefficientProEtaleModelTopology.{u, 0} X) A I) ⋙
        ConstantCompletion.res (sfbModelCompletionIso X I).hom :=
  isoWhiskerLeft (adicLisseConstantModules X A)
      (modelScalarChangeIso X (CompletedConstantReduction.base X I)) ≪≫
    isoWhiskerRight (modelConstantModulesIso X A)
      (ConstantCompletion.change ((sfbModelRings X).map (CompletedConstantReduction.base X I))) ≪≫
    isoWhiskerLeft
      (commutativeSiteConstantModuleFunctor (coefficientProEtaleModelTopology.{u, 0} X) A)
      (scalarChangeSquare ((sfbModelConstantsIso X).app (CommRingCat.of A))
        (sfbModelCompletionIso X I) _ _ (modelCoefficientMap X I))

/-- The transported actual completed complex is the scalar restriction of the normalized
completed coefficient complex. This is a comparison of cochain complexes, independent of
any completeness property.

Source: Bhatt--Scholze, Proposition 6.6.11, coefficient-model calculation;
Stacks Tags 03CY, 093J and 093M.
(auxiliary; not a blueprint node).

Proof: constant module realization in either presentation is the sheafification of the
same constant module presheaf. The equivalent-site sheafification comparison, normalized
on constant sections, gives a natural isomorphism between these realizations. The
canonical completed-ring comparison commutes with the coefficient maps, as can be
checked after every finite projection by naturality of constant sheafification.
Consequently the two scalar-extension functors have canonically isomorphic right
adjoints (restriction of scalars), and uniqueness of left adjoints gives their natural
comparison. Apply it degreewise to P. Naturality gives compatibility with differentials.
The termwise comparison and its inverse are chain maps by naturality. This is an
isomorphism before localization, so it applies to unbounded P, zero rings, I=0,
I=A and the empty site without any localization representative or completeness claim. -/
theorem sfbPerfectModel_complex_comparison (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    let F := proEtaleModuleToModel.{u} (X := X)
      ((adicLisseForget.{u} X).obj (adicLisseCompletedRing X I))
    Nonempty
      (((F.mapHomologicalComplex (.up ℤ)).obj
        (((completedAdicChange X (CompletedConstantReduction.base X I)).mapHomologicalComplex
          (.up ℤ)).obj ((CompletedConstantReduction.constantComplex X A).obj P))) ≅
        (((ConstantCompletion.res (sfbModelCompletionIso X I).hom).mapHomologicalComplex
          (.up ℤ)).obj
            (AdicPerfectModel.model (coefficientProEtaleModelTopology.{u, 0} X) I P))) := by
  let e := completedRealizationIso X A I
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun q ↦ e.app (P.X q)) ?_⟩
  intro i j _
  exact (e.hom.naturality (P.d i j)).symm

end AlgebraicGeometry.Scheme
