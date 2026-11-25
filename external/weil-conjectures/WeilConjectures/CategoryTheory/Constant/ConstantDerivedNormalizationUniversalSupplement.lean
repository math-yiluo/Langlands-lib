/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import Mathlib.CategoryTheory.Adjunction.Comma
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Constant realization preserves universal coefficient normalization

Source: Stacks Project, Tags 06YY, 07A4 and 0G7E.
(blueprint: lem-weil-pbc-constant-derived-normalization-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantNormalizationComparison
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R]

private def ringRestriction : realizationModules J R ⥤
    SheafOfModules.{max u v} ((constantSheaf J RingCat.{max u v}).obj (RingCat.of R)) :=
  SheafOfModules.restrictScalars (realizationRingIso J R).inv

private theorem ringRestriction_equivalence : (ringRestriction J R).IsEquivalence := by
  let eC : C ≌ C := Equivalence.refl
  let : eC.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let : eC.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let c := (realizationRingIso J R).symm
  let e := SheafOfModules.pushforwardPushforwardEquivalence.{max u v}
    (J := J) (K := J) eC c.hom c.inv
    (by
      ext U x
      dsimp [eC, Equivalence.refl]
      simp only [CategoryTheory.Functor.map_id]
      exact congrArg (fun f ↦ f.hom.app U x) c.inv_hom_id.symm)
    (by
      ext U x
      dsimp [eC, Equivalence.refl]
      simp only [CategoryTheory.Functor.map_id]
      exact congrArg (fun f ↦ f.hom.app U x) c.hom_inv_id)
  exact e.isEquivalence_functor

private instance : (ringRestriction J R).IsEquivalence := ringRestriction_equivalence J R

private instance : (constantRingModuleRestriction J R).IsEquivalence := by
  obtain ⟨⟨e, he, _⟩, _⟩ := constant_ring_module_sheaves J R
  rw [← he]
  infer_instance

private def restriction : realizationModules J R ⥤ Sheaf J (ModuleCat.{max u v} R) :=
  ringRestriction J R ⋙ constantRingModuleRestriction J R

private instance : (restriction J R).IsEquivalence := by unfold restriction; infer_instance
private instance : (restriction J R).Additive where
  map_add := by intros; ext U x; rfl
private instance : PreservesFiniteLimits (restriction J R) := inferInstance
private instance : PreservesFiniteColimits (restriction J R) := inferInstance

private lemma ringIso_fac : realizationRingUnit J R ≫ (realizationRingIso J R).hom.hom =
    toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)) := by
  dsimp only [realizationRingIso, Iso.app_hom]
  rw [constantCommuteCompose_hom_app_hom]
  unfold realizationRingUnit
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of R)
      (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)

private lemma restriction_smul (M : realizationModules J R) (V : Cᵒᵖ) (r : R) (x : M.val.obj V) :
    r • (show ((restriction J R).obj M).obj.obj V from x) =
      (realizationRingUnit J R).app V r • x := by
  have h := congrArg (fun f ↦ f.app V r) (ringIso_fac J R)
  have hi := congrArg (fun f ↦ f.hom.app V) (realizationRingIso J R).hom_inv_id
  change (realizationRingIso J R).inv.hom.app V
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app V r) • x = _
  erw [← h]
  exact congrArg (fun a ↦ a • x) (ConcreteCategory.congr_hom hi _)

private instance : Presheaf.IsLocallyInjective J (realizationRingUnit J R) :=
  (realizationRingUnit_locallyBijective J R).1
private instance : Presheaf.IsLocallySurjective J (realizationRingUnit J R) :=
  (realizationRingUnit_locallyBijective J R).2

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

private def constantSeed (M : ModuleCat.{max u v} R) :
    (Functor.const Cᵒᵖ).obj M ⟶
      ((restriction J R).obj ((commutativeSiteConstantModuleFunctor J R).obj M)).obj where
  app V := by
    refine ConcreteCategory.ofHom (C := ModuleCat.{max u v} R) ?_
    refine { toFun := fun x ↦ ?_, map_add' := ?_, map_smul' := ?_ }
    · exact ((PresheafOfModules.sheafificationAdjunction
        (realizationRingUnit J R)).unit.app
          ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V x
    · intros; apply map_add
    · intro r x
      rw [restriction_smul]
      exact (((PresheafOfModules.sheafificationAdjunction
        (realizationRingUnit J R)).unit.app
          ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V).hom.map_smul r x
  naturality V W f := by
    ext x
    exact (PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
        ((siteConstantModulePresheafGeneral (C := C) R).obj M)) f x)

private def constantMap (M : ModuleCat.{max u v} R) :
    (constantSheaf J (ModuleCat.{max u v} R)).obj M ⟶
      (restriction J R).obj ((commutativeSiteConstantModuleFunctor J R).obj M) :=
  ((sheafificationAdjunction J (ModuleCat.{max u v} R)).homEquiv _ _).symm
    (constantSeed J R M)

private lemma constantMap_fac (M : ModuleCat.{max u v} R) :
    toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫ (constantMap J R M).hom =
      constantSeed J R M := by
  exact ((sheafificationAdjunction J (ModuleCat.{max u v} R)).homEquiv _ _).apply_symm_apply _

private instance (M : ModuleCat.{max u v} R) :
    Presheaf.IsLocallyInjective J (constantSeed J R M) where
  equalizerSieve_mem x y h :=
    Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj
        ((forget₂ (ModuleCat R) AddCommGrpCat).obj M))) x y h

private instance (M : ModuleCat.{max u v} R) :
    Presheaf.IsLocallySurjective J (constantSeed J R M) where
  imageSieve_mem x :=
    Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj
        ((forget₂ (ModuleCat R) AddCommGrpCat).obj M))) x

private instance (M : ModuleCat.{max u v} R) : IsIso (constantMap J R M) := by
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · apply (Presheaf.comp_isLocallyInjective_iff J
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (constantMap J R M).hom).mp
    rw [constantMap_fac]
    infer_instance
  · apply (Presheaf.comp_isLocallySurjective_iff J
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (constantMap J R M).hom).mp
    rw [constantMap_fac]
    infer_instance

private theorem constantMap_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    (constantSheaf J (ModuleCat.{max u v} R)).map f ≫ constantMap J R N =
      constantMap J R M ≫ (restriction J R).map
        ((commutativeSiteConstantModuleFunctor J R).map f) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    (((restriction J R).obj ((commutativeSiteConstantModuleFunctor J R).obj N)).property)
  change toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
    ((constantSheaf J (ModuleCat.{max u v} R)).map f).hom ≫ (constantMap J R N).hom = _
  erw [← Category.assoc, ← toSheafify_naturality, Category.assoc, constantMap_fac]
  change _ = toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
    (constantMap J R M).hom ≫ _
  rw [← Category.assoc, constantMap_fac]
  ext V x
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J
      ((Functor.const Cᵒᵖ).map ((forget₂ (ModuleCat R) AddCommGrpCat).map f))) V) x

private def constantIso : constantSheaf J (ModuleCat.{max u v} R) ≅
    commutativeSiteConstantModuleFunctor J R ⋙ restriction J R :=
  NatIso.ofComponents (fun M ↦ asIso (constantMap J R M))
    (fun f ↦ constantMap_naturality J R f)

variable {S : Type (max u v)} [CommRing S] (q : R →+* S)

private lemma ringUnit_naturality :
    (Functor.const Cᵒᵖ).map (RingCat.ofHom q) ≫ realizationRingUnit J S =
      realizationRingUnit J R ≫ ((sheafCompose J
        (forget₂ CommRingCat RingCat)).map
          ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q))).hom := by
  have h := toSheafify_naturality J
    ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom q))
  exact congrArg (fun f ↦ Functor.whiskerRight f (forget₂ CommRingCat RingCat)) h

private lemma coefficient_smul (M : realizationModules J S) (V : Cᵒᵖ) (r : R)
    (x : M.val.obj V) :
    r • (show ((restriction J R).obj
      ((ConstantScalarRealization.restriction J q).obj M)).obj.obj V from x) =
      q r • (show ((restriction J S).obj M).obj.obj V from x) := by
  trans (realizationRingUnit J R).app V r •
    (show ((ConstantScalarRealization.restriction J q).obj M).val.obj V from x)
  · exact restriction_smul J R ((ConstantScalarRealization.restriction J q).obj M) V r x
  · trans (realizationRingUnit J S).app V (q r) • x
    · change (((sheafCompose J (forget₂ CommRingCat RingCat)).map
        ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q))).hom.app V
          ((realizationRingUnit J R).app V r)) • x = _
      exact congrArg (fun a ↦ a • x)
        (congrArg (fun f ↦ f.app V r) (ringUnit_naturality J R q)).symm
    · exact (restriction_smul J S M V (q r) x).symm

private def coefficientIso : ConstantScalarRealization.restriction J q ⋙ restriction J R ≅
    restriction J S ⋙ Sheaf.restrictScalars J q := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply ObjectProperty.isoMk
    refine NatIso.ofComponents (fun V ↦ ?_) ?_
    · refine
        { hom := ConcreteCategory.ofHom (C := ModuleCat.{max u v} R)
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by intros; exact coefficient_smul J R q M V _ _ }
          inv := ConcreteCategory.ofHom (C := ModuleCat.{max u v} R)
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by intros; exact (coefficient_smul J R q M V _ _).symm }
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }
    · intros; ext x; rfl
  · intros; apply Sheaf.hom_ext; ext V x; rfl

private lemma constantRestrict_hom_unit (M : ModuleCat.{max u v} S) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
        (ModuleCat.restrictScalars q) ≫
      ((constantCommuteCompose J (ModuleCat.restrictScalars q)).hom.app M).hom =
    toSheafify J ((Functor.const Cᵒᵖ).obj ((ModuleCat.restrictScalars q).obj M)) := by
  rw [constantCommuteCompose_hom_app_hom]
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality J
    (Functor.constComp Cᵒᵖ M (ModuleCat.restrictScalars q)).hom).symm.trans (by rfl)

private lemma constantRestrict_inv_unit (M : ModuleCat.{max u v} S) :
    toSheafify J ((Functor.const Cᵒᵖ).obj ((ModuleCat.restrictScalars q).obj M)) ≫
        ((constantCommuteCompose J (ModuleCat.restrictScalars q)).inv.app M).hom =
      Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
        (ModuleCat.restrictScalars q) := by
  let c := (constantCommuteCompose J (ModuleCat.restrictScalars q)).app M
  have hi : c.inv.hom ≫ c.hom.hom = 𝟙 _ := congrArg (fun f ↦ f.hom) c.inv_hom_id
  apply (cancel_mono c.hom.hom).mp
  change (toSheafify J _ ≫ c.inv.hom) ≫ c.hom.hom = _
  rw [Category.assoc, hi]
  erw [Category.comp_id]
  exact (constantRestrict_hom_unit J R q M).symm

private lemma constantCoefficient_pasting (M : ModuleCat.{max u v} S) :
    (constantCommuteCompose J (ModuleCat.restrictScalars q)).inv.app M ≫
      (Sheaf.restrictScalars J q).map ((constantIso J S).hom.app M) =
    (constantIso J R).hom.app ((ModuleCat.restrictScalars q).obj M) ≫
      (restriction J R).map ((ConstantScalarRealization.restrictionIso J q).inv.app M) ≫
      (coefficientIso J R q).hom.app ((commutativeSiteConstantModuleFunctor J S).obj M) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    (((restriction J S ⋙ Sheaf.restrictScalars J q).obj
      ((commutativeSiteConstantModuleFunctor J S).obj M)).property)
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  erw [← Category.assoc, constantRestrict_inv_unit]
  change Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
      (ModuleCat.restrictScalars q) ≫
      Functor.whiskerRight (constantMap J S M).hom (ModuleCat.restrictScalars q) = _
  rw [← Functor.whiskerRight_comp, constantMap_fac]
  change _ = toSheafify J ((Functor.const Cᵒᵖ).obj
    ((ModuleCat.restrictScalars q).obj M)) ≫
      (constantMap J R ((ModuleCat.restrictScalars q).obj M)).hom ≫ _
  rw [← Category.assoc, constantMap_fac]
  ext V x
  have hc := (Classical.choose_spec
    (ConstantScalarRealization.restrictionIso_existsUnique J q)).1 M V x
  have hi := congrArg (fun f ↦ f.val.app V)
    ((ConstantScalarRealization.restrictionIso J q).app M).hom_inv_id
  have hix := ConcreteCategory.congr_hom hi
    (ConstantScalarRealization.constantSection J M V x)
  change ((ConstantScalarRealization.restrictionIso J q).inv.app M).val.app V
      (((ConstantScalarRealization.restrictionIso J q).hom.app M).val.app V
        (ConstantScalarRealization.constantSection J M V x)) = _ at hix
  erw [hc] at hix
  exact hix.symm

end CategoryTheory.ConstantNormalizationComparison

namespace CategoryTheory.ConstantNormalizationComparison
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (R : Type (u + 1)) [CommRing R]
  {S : Type (u + 1)} [CommRing S] (q : R →+* S)

private local instance (A : Type (u + 1)) [CommRing A] :
    HasDerivedCategory.{(u + 1) + 1} (realizationModules.{u + 1, u} J A) :=
  HasDerivedCategory.standard (realizationModules.{u + 1, u} J A)

private def ringedNormalization
    {E : DerivedCategory (ModuleCat.{u + 1} R)}
    {E' : DerivedCategory (ModuleCat.{u + 1} S)}
    (d : E ⟶ (ConstantScalarRealization.moduleDerivedRestriction q).obj E') :=
  (commutativeSiteDerivedConstantModuleFunctor J R).map d ≫
    (ConstantScalarRealization.derivedRestrictionIso J q).inv.app E'

private theorem ringedNormalization_universal
    {E : DerivedCategory (ModuleCat.{u + 1} R)}
    {E' : DerivedCategory (ModuleCat.{u + 1} S)}
    (d : E ⟶ (ConstantScalarRealization.moduleDerivedRestriction q).obj E')
    (h : StructuredArrow.IsUniversal (StructuredArrow.mk d)) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (ringedNormalization J R q d) : StructuredArrow
        ((commutativeSiteDerivedConstantModuleFunctor J R).obj E)
        (ConstantScalarRealization.derivedRestriction J q))) := by
  let a := ConstantScalarRealization.moduleDerivedAdjunction q
  let b := ConstantScalarRealization.derivedAdjunction J q
  let e := (mkInitialOfLeftAdjoint _ a E).uniqueUpToIso h
  let α : (ConstantScalarRealization.moduleDerivedExtension q).obj E ≅ E' :=
    (StructuredArrow.proj E
      (ConstantScalarRealization.moduleDerivedRestriction q)).mapIso e
  have hα : a.unit.app E ≫
      (ConstantScalarRealization.moduleDerivedRestriction q).map α.hom = d := e.hom.w
  obtain ⟨hcomp, _, hunit⟩ :=
    ConstantScalarRealization.constantRealizationDerivedScalarExtension J q
  let := hcomp
  have : IsIso (ConstantScalarRealization.comparison J q E) :=
    NatIso.isIso_app_of_isIso (ConstantScalarRealization.comparisonTransformation J q) E
  let t := asIso (ConstantScalarRealization.comparison J q E) ≪≫
    (commutativeSiteDerivedConstantModuleFunctor J S).mapIso α
  have ht : b.unit.app ((commutativeSiteDerivedConstantModuleFunctor J R).obj E) ≫
      (ConstantScalarRealization.derivedRestriction J q).map t.hom =
      ringedNormalization J R q d := by
    apply (cancel_mono ((ConstantScalarRealization.derivedRestrictionIso J q).hom.app E')).mp
    simp only [t, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
      CategoryTheory.Functor.map_comp, Category.assoc, ringedNormalization,
      Iso.inv_hom_id_app]
    have hn := (ConstantScalarRealization.derivedRestrictionIso J q).hom.naturality α.hom
    dsimp only [Functor.comp_map] at hn
    erw [hn, reassoc_of% hunit E, ← CategoryTheory.Functor.map_comp, hα, Category.comp_id]
  let i : (StructuredArrow.mk
      (b.unit.app ((commutativeSiteDerivedConstantModuleFunctor J R).obj E)) :
      StructuredArrow _ (ConstantScalarRealization.derivedRestriction J q)) ≅
      StructuredArrow.mk (ringedNormalization J R q d) := StructuredArrow.isoMk t ht
  exact ⟨(mkInitialOfLeftAdjoint _ b
    ((commutativeSiteDerivedConstantModuleFunctor J R).obj E)).ofIso i⟩

private def derivedConstantIso :
    normalizationConstant (R := R) J ≅
      commutativeSiteDerivedConstantModuleFunctor J R ⋙
        (restriction J R).mapDerivedCategory :=
  Functor.mapDerivedCategoryTriangleIso (constantIso J R)

private def derivedCoefficientIso :
    (ConstantScalarRealization.restriction J q).mapDerivedCategory ⋙
        (restriction J R).mapDerivedCategory ≅
      (restriction J S).mapDerivedCategory ⋙ normalizationRestrict J q :=
  Functor.mapDerivedCategorySquareIso (coefficientIso J R q)

private theorem derivedCoefficient_pasting (E' : DerivedCategory (ModuleCat.{u + 1} S)) :
    (normalizationConstantRestrict J q).inv.app E' ≫
        (normalizationRestrict J q).map ((derivedConstantIso J S).hom.app E') =
      (derivedConstantIso J R).hom.app ((normalizationModuleRestrict q).obj E') ≫
        (restriction J R).mapDerivedCategory.map
          ((ConstantScalarRealization.derivedRestrictionIso J q).inv.app E') ≫
        (derivedCoefficientIso J R q).hom.app
          ((commutativeSiteDerivedConstantModuleFunctor J S).obj E') := by
  convert! Functor.mapDerivedCategorySquareIso_hom_app_comp
    (ConstantScalarRealization.restrictionIso J q).symm
    (coefficientIso J R q)
    (constantCommuteCompose J
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).symm
    (constantIso J R) (constantIso J S) (constantCoefficient_pasting J R q) E' using 1 <;>
  simp only [Functor.mapDerivedCategorySquareIso, derivedConstantIso,
    derivedCoefficientIso, normalizationConstantRestrict,
    ConstantScalarRealization.derivedRestrictionIso, Iso.symm_inv, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  all_goals rfl

private theorem normalization_transport
    {E : DerivedCategory (ModuleCat.{u + 1} R)}
    {E' : DerivedCategory (ModuleCat.{u + 1} S)}
    (d : E ⟶ (normalizationModuleRestrict q).obj E') :
    (derivedConstantIso J R).hom.app E ≫
        (restriction J R).mapDerivedCategory.map (ringedNormalization J R q d) ≫
        (derivedCoefficientIso J R q).hom.app
          ((commutativeSiteDerivedConstantModuleFunctor J S).obj E') =
      normalizationConstantArrow J q d ≫
        (normalizationRestrict J q).map ((derivedConstantIso J S).hom.app E') := by
  dsimp only [ringedNormalization, normalizationConstantArrow]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (derivedConstantIso J R).hom.naturality d]
  rw [← derivedCoefficient_pasting J R q E']

private theorem fixedNormalization_universal
    {E : DerivedCategory (ModuleCat.{u + 1} R)}
    {E' : DerivedCategory (ModuleCat.{u + 1} S)}
    (d : E ⟶ (normalizationModuleRestrict q).obj E')
    (h : Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk d))) :
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (normalizationConstantArrow J q d) :
        StructuredArrow ((normalizationConstant J).obj E)
          (normalizationRestrict J q))) := by
  obtain ⟨hr⟩ := ringedNormalization_universal J R q d h.some
  let T := StructuredArrow.map₂
    (R := ConstantScalarRealization.derivedRestriction J q)
    (G := (restriction J R).mapDerivedCategory)
    (F := (restriction J S).mapDerivedCategory)
    (R' := normalizationRestrict J q)
    ((derivedConstantIso J R).hom.app E) (derivedCoefficientIso J R q).hom
  have hi := hr.isInitialObj T _
  let e : (restriction J S).mapDerivedCategory.obj
      ((commutativeSiteDerivedConstantModuleFunctor J S).obj E') ≅
      (normalizationConstant J).obj E' := (derivedConstantIso J S).symm.app E'
  have he : (T.obj (StructuredArrow.mk (ringedNormalization J R q d))).hom ≫
      (normalizationRestrict J q).map e.hom = normalizationConstantArrow J q d := by
    change ((derivedConstantIso J R).hom.app E ≫
      (restriction J R).mapDerivedCategory.map (ringedNormalization J R q d) ≫
      (derivedCoefficientIso J R q).hom.app
        ((commutativeSiteDerivedConstantModuleFunctor J S).obj E')) ≫
      (normalizationRestrict J q).map ((derivedConstantIso J S).inv.app E') = _
    rw [normalization_transport]
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  exact ⟨hi.ofIso (StructuredArrow.isoMk
    (f := T.obj (StructuredArrow.mk (ringedNormalization J R q d)))
    (f' := StructuredArrow.mk (normalizationConstantArrow J q d)) e he)⟩

end CategoryTheory.ConstantNormalizationComparison

namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]

/-- Exact constant realization preserves the specified universal coefficient arrow.
This is a scalar-extension property of constants on a site, independently of covers,
local systems, Isom sheaves or their evaluations.

Source: Stacks Project, Tags 06YY, 07A4 and 0G7E.
(blueprint: lem-weil-pbc-constant-derived-normalization-universal).

Proof: compare fixed-ring module sheaves with modules over the constant ring sheaf.
Restriction along the canonical ring isomorphism and the constant-ring module
comparison give an additive exact equivalence. Construct the constant comparison by
sheafifying the coefficient-realization unit; its local bijectivity makes it an
isomorphism. On constant sections it commutes with coefficient restriction. Exact
localization transports this identity to derived categories. The existing ringed
constant-realization scalar-extension theorem makes the corresponding ringed arrow
universal, by uniqueness of universal arrows and its unit identity. The exact
comparison equivalences induce an equivalence of structured-arrow categories, and
the localized coefficient identity identifies the transported arrow with the stated
normalizationConstantArrow. Equivalences preserve initial objects, giving the result.
No finiteness, nonempty-site or boundedness assumption enters this argument. -/
theorem normalizationConstantArrow_isUniversal
    (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (q : R →+* S) {E : DerivedCategory (ModuleCat.{u + 1} R)}
    {E' : DerivedCategory (ModuleCat.{u + 1} S)}
    (d : E ⟶ (normalizationModuleRestrict q).obj E')
    (h : Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk d))) :
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (normalizationConstantArrow J q d))) := by
  exact ConstantNormalizationComparison.fixedNormalization_universal J R q d h

end CategoryTheory
