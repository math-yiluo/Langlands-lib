/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectQuotientSectionModel
import all WeilConjectures.AlgebraicGeometry.AdicPerfectQuotientSectionComparisonTensor
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Constant quotient sections and scalar transitions

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK; Tag 09C6.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] derivedExtension extend change
  adicPerfectQuotientModuleStep
  AdicQuotientSections.rightAdjoint AdicQuotientSections.adjunction
  AdicQuotientSections.step

attribute [local irreducible] AdicQuotientSections.localConstantIso
  AdicQuotientSections.sectionsIso adicFiniteChangeComp

section NormalizedRealization
attribute [local implicit_reducible] sheafCompose Functor.sheafPushforwardContinuous
  ConstantCompletion.quotient AdicCohomology.quotient

attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
  {A : Type w} [CommRing A] (J : Ideal A) (U : C)

private abbrev comparisonLocalFunctor : ModuleCat.{w} A ⥤
    Mod ((completed T A J).over U) :=
  modelPresentationFunctor T A ⋙ change (coefficientMap T A J) ⋙
    SheafOfModules.overFunctor _ U

private abbrev comparisonProjection (n : ℕ) :=
  (T.overPullback CommRingCat U).map (projection T A J n)

private abbrev comparisonScalarStep (n : ℕ) :=
  (T.overPullback CommRingCat U).map (transition T A J n)

private theorem comparisonScalarStep_comp (n : ℕ) :
    comparisonProjection T J U (n + 1) ≫ comparisonScalarStep T J U n =
      comparisonProjection T J U n := by
  let V := T.overPullback CommRingCat U
  dsimp only [comparisonProjection, comparisonScalarStep]
  rw [← V.map_comp]
  congr 1
  simpa only [completed, projection, finiteSystem, Functor.ofOpSequence_map_homOfLE_succ]
    using (limit.w (finiteSystem T A J) (homOfLE (Nat.le_succ n)).op)

private abbrev comparisonQuotientFunctor (n : ℕ) : ModuleCat.{w} A ⥤
    Mod ((finite T A J n).over U) :=
  comparisonLocalFunctor T J U ⋙ change (comparisonProjection T J U n)

private def comparisonModuleStep (n : ℕ) :
    comparisonQuotientFunctor T J U (n + 1) ⋙ change (comparisonScalarStep T J U n) ≅
      comparisonQuotientFunctor T J U n :=
  functorScalarCompIso (T.over U)
    (comparisonProjection T J U (n + 1)) (comparisonScalarStep T J U n)
    (comparisonLocalFunctor T J U) (comparisonProjection T J U n)
    (comparisonScalarStep_comp T J U n)

private abbrev comparisonQuotientMap (n : ℕ) :=
  (T.overPullback CommRingCat U).map (ConstantCompletion.quotient T A J n)

private abbrev comparisonQuotientRealization (n : ℕ) :=
  AdicQuotientSections.localConstant T A U ⋙ change (comparisonQuotientMap T J U n)

private abbrev comparisonRawRightAdjoint (n : ℕ) :=
  res (comparisonQuotientMap T J U n) ⋙ AdicQuotientSections.localSections T A U

private def modelGenerator (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ)
    (x : M) : ((comparisonLocalFunctor T J U).obj M).val.obj V :=
  rawModelGenerator T J U M V x

private theorem modelGenerator_eq (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ) (x : M) :
    modelGenerator T J U M V x = rawModelGenerator T J U M V x := by
  unfold modelGenerator
  rfl

private def quotientGenerator (n : ℕ) (M : ModuleCat.{w} A)
    (V : (Over U)ᵒᵖ) (x : M) : ((comparisonQuotientFunctor T J U n).obj M).val.obj V := by
  unfold comparisonQuotientFunctor
  exact tensorSection (comparisonProjection T J U n)
    (((change (coefficientMap T A J)).obj
      ((modelPresentationFunctor T A).obj M)).over U) V 1 (modelGenerator T J U M V x)

private def directRealization (n : ℕ) : comparisonQuotientFunctor T J U n ≅
    commutativeSiteConstantModuleFunctor T A ⋙
      change (ConstantCompletion.quotient T A J n) ⋙ SheafOfModules.overFunctor _ U := by
  unfold comparisonQuotientFunctor comparisonLocalFunctor
  exact directIso T (coefficientMap T A J) (projection T A J n) U
    (modelPresentationIso T A) (ConstantCompletion.quotient T A J n)
    (completionConeEq T J n)

attribute [irreducible] directRealization modelGenerator quotientGenerator

private theorem quotientGenerator_eq (n : ℕ) (M : ModuleCat.{w} A)
    (V : (Over U)ᵒᵖ) (x : M) :
    quotientGenerator T J U n M V x =
      tensorSection (comparisonProjection T J U n)
        (((change (coefficientMap T A J)).obj
      ((modelPresentationFunctor T A).obj M)).over U) V 1 (modelGenerator T J U M V x) := by
  unfold quotientGenerator
  rfl

private theorem directRealization_eq (n : ℕ) :
    directRealization T J U n =
      directIso T (coefficientMap T A J) (projection T A J n) U
        (modelPresentationIso T A) (ConstantCompletion.quotient T A J n)
        (completionConeEq T J n) := by
  unfold directRealization
  rfl

private theorem directRealization_one (n : ℕ) (M : ModuleCat.{w} A)
    (V : (Over U)ᵒᵖ) (x : M) :
    natSection (T.over U) (directRealization T J U n).hom M V
        (quotientGenerator T J U n M V x) =
      rawDirectGenerator T J U n M V x := by
  rw [directRealization_eq, quotientGenerator_eq, modelGenerator_eq]
  exact rawDirectGenerator_one T J U n M V x

private def normalizedRealization (n : ℕ) : comparisonQuotientFunctor T J U n ≅
    comparisonQuotientRealization T J U n :=
  sliceRealizationIso T U (ConstantCompletion.quotient T A J n)
    (directRealization T J U n) (AdicQuotientSections.localConstantIso T A U)

attribute [irreducible] normalizedRealization

private def normalizedAdjunction (n : ℕ) : comparisonQuotientFunctor T J U n ⊣
    comparisonRawRightAdjoint T J U n :=
  normalizedSectionsAdjunction T U (comparisonQuotientMap T J U n)
    (normalizedRealization T J U n)

attribute [irreducible] normalizedAdjunction

private def sheafQuotientIso (n : ℕ) :
    comparisonQuotientFunctor T J U n ⋙
        res (comparisonQuotientMap T J U n) ≅
      AdicCohomology.quotient J (n + 1) ⋙
        AdicQuotientSections.localConstant
          T A U :=
  sliceQuotientIso T U (ConstantCompletion.quotient T A J n) (directRealization T J U n)
    (constantQuotientIso T J (n + 1)) (AdicQuotientSections.localConstantIso T A U)

attribute [irreducible] sheafQuotientIso

private def rawComparison (n : ℕ) :
    AdicCohomology.quotient J (n + 1) ⋙ AdicCohomology.sections
        (T.over U) (Over.mk (𝟙 U)) ≅
      comparisonQuotientFunctor T J U n ⋙
        comparisonRawRightAdjoint T J U n :=
  isoWhiskerLeft _ (AdicQuotientSections.sectionsIso
      T A U) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (sheafQuotientIso T J U n).symm _ ≪≫
    Functor.associator _ _ _

attribute [irreducible] rawComparison

private theorem normalizedRealization_one (n : ℕ) (M : ModuleCat.{w} A)
    (V : (Over U)ᵒᵖ) (x : M) :
    natSection (T.over U) (normalizedRealization T J U n).hom M V
        (quotientGenerator T J U n M V x) =
      tensorSection (comparisonQuotientMap T J U n)
        ((AdicQuotientSections.localConstant
          T A U).obj M) V 1
        (localGenerator T U M V x) := by
  unfold normalizedRealization
  apply sliceRealizationIso_generator T U (ConstantCompletion.quotient T A J n)
    (directRealization T J U n) (AdicQuotientSections.localConstantIso T A U) M V
    (quotientGenerator T J U n M V x)
    (ConstantScalarRealization.constantSection T M (op V.unop.left) x)
    (localGenerator T U M V x)
  · rw [directRealization_one, rawDirectGenerator_eq]
  · exact localConstantIso_inv_generator T U M V x

private theorem sheafQuotientIso_one (n : ℕ) (M : ModuleCat.{w} A)
    (V : (Over U)ᵒᵖ) (x : M) :
    natSection (T.over U) (sheafQuotientIso T J U n).hom M V
        (sectionRes (T.over U) (comparisonQuotientMap T J U n)
          ((comparisonQuotientFunctor T J U n).obj M) V
          (quotientGenerator T J U n M V x)) =
      localGenerator T U
        ((AdicCohomology.quotient J (n + 1)).obj M) V (Submodule.Quotient.mk x) := by
  unfold sheafQuotientIso
  rw [sliceQuotientIso_apply, directRealization_one, rawDirectGenerator_eq, sectionUnder_over]
  dsimp only [ConstantCompletion.quotient]
  rw [constantQuotientIso_one, localConstantIso_inv_generator]

private theorem sheafQuotientIso_inv_generator (n : ℕ)
    (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ) (x : M) :
    natSection (T.over U) (sheafQuotientIso T J U n).inv M V
        (localGenerator T U
          ((AdicCohomology.quotient J (n + 1)).obj M) V (Submodule.Quotient.mk x)) =
      sectionRes (T.over U) (comparisonQuotientMap T J U n)
        ((comparisonQuotientFunctor T J U n).obj M) V
        (quotientGenerator T J U n M V x) := by
  rw [← sheafQuotientIso_one T J U n M V x]
  exact natSection_inv_hom (T.over U) (sheafQuotientIso T J U n) M V
    (sectionRes (T.over U) (comparisonQuotientMap T J U n)
      ((comparisonQuotientFunctor T J U n).obj M) V (quotientGenerator T J U n M V x))

private theorem quotientGenerator_step (n : ℕ) (M : ModuleCat.{w} A)
    (V : (Over U)ᵒᵖ) (x : M) :
    natSection (T.over U) (comparisonModuleStep T J U n).hom M V
        (tensorSection (comparisonScalarStep T J U n)
          ((comparisonQuotientFunctor T J U (n + 1)).obj M) V 1
            (quotientGenerator T J U (n + 1) M V x)) =
      quotientGenerator T J U n M V x := by
  unfold comparisonModuleStep
  rw [quotientGenerator_eq, quotientGenerator_eq]
  exact functorScalarCompIso_one (T.over U)
    (comparisonProjection T J U (n + 1)) (comparisonScalarStep T J U n)
    (comparisonLocalFunctor T J U) (comparisonProjection T J U n)
    (comparisonScalarStep_comp T J U n) M V (modelGenerator T J U M V x)

private theorem quotientMap_step (n : ℕ) :
    comparisonQuotientMap T J U (n + 1) ≫
        comparisonScalarStep T J U n =
      comparisonQuotientMap T J U n := by
  let V := T.overPullback CommRingCat U
  dsimp only [comparisonQuotientMap, comparisonScalarStep]
  rw [← V.map_comp]
  apply congrArg V.map
  have h := quotient_step T A J n
  simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, finiteSystem,
    Functor.ofOpSequence_map_homOfLE_succ] using h.symm

private def rawStep (n : ℕ) : comparisonRawRightAdjoint T J U (n + 1) ⟶
    change (comparisonScalarStep T J U n) ⋙
      comparisonRawRightAdjoint T J U n :=
  whiskerRight (insertionStep (T.over U)
      (comparisonQuotientMap T J U (n + 1))
      (comparisonScalarStep T J U n) (comparisonQuotientMap T J U n)
      (quotientMap_step T J U n))
    (AdicQuotientSections.localSections T A U) ≫
    (Functor.associator _ _ _).hom

attribute [irreducible] rawStep

private theorem rawStep_section (n : ℕ)
    (N : Mod ((finite T A J (n + 1)).over U))
    (x : N.val.obj (op (Over.mk (𝟙 U)))) :
    moduleValue (rawStep T J U n) N
        (terminalSection T U (comparisonQuotientMap T J U (n + 1)) N x) =
      terminalSection T U (comparisonQuotientMap T J U n)
        ((change (comparisonScalarStep T J U n)).obj N)
        (tensorSection (comparisonScalarStep T J U n) N (op (Over.mk (𝟙 U))) 1 x) := by
  unfold moduleValue rawStep terminalSection
  exact insertionStep_section (T.over U)
    (comparisonQuotientMap T J U (n + 1))
    (comparisonScalarStep T J U n) (comparisonQuotientMap T J U n)
    (quotientMap_step T J U n) N (op (Over.mk (𝟙 U))) x

private theorem normalizedAdjunction_unit (n : ℕ)
    (M : ModuleCat.{w} A) (x : M) :
    moduleValue (normalizedAdjunction T J U n).unit M x =
      terminalSection T U (comparisonQuotientMap T J U n)
        ((comparisonQuotientFunctor T J U n).obj M)
        (quotientGenerator T J U n M (op (Over.mk (𝟙 U))) x) := by
  unfold normalizedAdjunction
  exact normalizedSectionsAdjunction_unit_generator T U (comparisonQuotientMap T J U n)
    (normalizedRealization T J U n) M x
    (quotientGenerator T J U n M (op (Over.mk (𝟙 U))) x)
    (normalizedRealization_one T J U n M (op (Over.mk (𝟙 U))) x)

private theorem rawStep_unit (n : ℕ) (M : ModuleCat.{w} A) :
    (normalizedAdjunction T J U n).unit.app M =
      (normalizedAdjunction T J U (n + 1)).unit.app M ≫
        (rawStep T J U n).app ((comparisonQuotientFunctor T J U (n + 1)).obj M) ≫
        (comparisonRawRightAdjoint T J U n).map
          ((comparisonModuleStep T J U n).hom.app M) := by
  exact terminalUnit_compat T U
    (comparisonQuotientMap T J U n) (comparisonQuotientMap T J U (n + 1))
    (comparisonScalarStep T J U n)
    (normalizedAdjunction T J U n) (normalizedAdjunction T J U (n + 1))
    (rawStep T J U n) (comparisonModuleStep T J U n)
    (fun N x ↦ quotientGenerator T J U n N (op (Over.mk (𝟙 U))) x)
    (fun N x ↦ quotientGenerator T J U (n + 1) N (op (Over.mk (𝟙 U))) x)
    (normalizedAdjunction_unit T J U n) (normalizedAdjunction_unit T J U (n + 1))
    (rawStep_section T J U n)
    (fun N x ↦ quotientGenerator_step T J U n N (op (Over.mk (𝟙 U))) x) M

private theorem quotientTransition_mk (n : ℕ) (M : ModuleCat.{w} A) (x : M) :
    ((AdicCohomology.transition J
      (Nat.add_le_add_right (Nat.le_succ n) 1)).app M).hom
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

private theorem sheafComparison_square (n : ℕ) (M : ModuleCat.{w} A) :
    (AdicQuotientSections.localConstant
        T A U).map
        ((AdicCohomology.transition J
          (Nat.add_le_add_right (Nat.le_succ n) 1)).app M) ≫
      (sheafQuotientIso T J U n).inv.app M =
    (sheafQuotientIso T J U (n + 1)).inv.app M ≫
      (insertionStep (T.over U)
        (comparisonQuotientMap T J U (n + 1))
        (comparisonScalarStep T J U n) (comparisonQuotientMap T J U n)
        (quotientMap_step T J U n)).app ((comparisonQuotientFunctor T J U (n + 1)).obj M) ≫
      (res (comparisonQuotientMap T J U n)).map
        ((comparisonModuleStep T J U n).hom.app M) := by
  let δ := AdicCohomology.transition J (Nat.add_le_add_right (Nat.le_succ n) 1)
  refine comparisonSquare_of_generators T U
    (comparisonQuotientMap T J U n) (comparisonQuotientMap T J U (n + 1))
    (comparisonScalarStep T J U n) (quotientMap_step T J U n)
    (AdicCohomology.quotient J (n + 1)) (AdicCohomology.quotient J (n + 2)) δ
    (sheafQuotientIso T J U n) (sheafQuotientIso T J U (n + 1))
    (comparisonModuleStep T J U n) (fun N ↦ N) (fun _ x ↦ Submodule.Quotient.mk x)
    (fun N ↦ Submodule.Quotient.mk_surjective (AdicCohomology.power J N (n + 2))) ?_ M
  intro N V x
  exact generatorComparison_square T U
    (comparisonQuotientMap T J U n) (comparisonQuotientMap T J U (n + 1))
    (comparisonScalarStep T J U n) (quotientMap_step T J U n)
    (AdicCohomology.quotient J (n + 1)) (AdicCohomology.quotient J (n + 2)) δ
    (sheafQuotientIso T J U n) (sheafQuotientIso T J U (n + 1))
    (comparisonModuleStep T J U n) N V (Submodule.Quotient.mk x)
    (quotientGenerator T J U n N V x) (quotientGenerator T J U (n + 1) N V x)
    (by
      change natSection (T.over U) (sheafQuotientIso T J U n).inv N V
        (localGenerator T U ((AdicCohomology.quotient J (n + 1)).obj N) V
          (((AdicCohomology.transition J
            (Nat.add_le_add_right (Nat.le_succ n) 1)).app N).hom
              (Submodule.Quotient.mk x))) = _
      rw [quotientTransition_mk]
      exact sheafQuotientIso_inv_generator T J U n N V x)
    (sheafQuotientIso_inv_generator T J U (n + 1) N V x)
    (quotientGenerator_step T J U n N V x)

private theorem rawComparison_hom_app (n : ℕ) (M : ModuleCat.{w} A) :
    (rawComparison T J U n).hom.app M =
      (AdicQuotientSections.sectionsIso
        T A U).hom.app
          ((AdicCohomology.quotient J (n + 1)).obj M) ≫
      (AdicQuotientSections.localSections
        T A U).map
          ((sheafQuotientIso T J U n).inv.app M) := by
  simp only [rawComparison, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp]

private theorem rawComparison_square (n : ℕ) (M : ModuleCat.{w} A) :
    (AdicCohomology.sections
        (T.over U) (Over.mk (𝟙 U))).map
        ((AdicCohomology.transition J
          (Nat.add_le_add_right (Nat.le_succ n) 1)).app M) ≫
      (rawComparison T J U n).hom.app M =
    (rawComparison T J U (n + 1)).hom.app M ≫
      (rawStep T J U n).app ((comparisonQuotientFunctor T J U (n + 1)).obj M) ≫
      (comparisonRawRightAdjoint T J U n).map
        ((comparisonModuleStep T J U n).hom.app M) := by
  let L := AdicQuotientSections.localConstant T A U
  let S := AdicQuotientSections.localSections T A U
  let δ := (AdicCohomology.transition J
    (Nat.add_le_add_right (Nat.le_succ n) 1)).app M
  let i := AdicQuotientSections.sectionsIso T A U
  have hn : (AdicCohomology.sections (T.over U) (Over.mk (𝟙 U))).map δ ≫
      i.hom.app ((AdicCohomology.quotient J (n + 1)).obj M) =
    i.hom.app ((AdicCohomology.quotient J (n + 2)).obj M) ≫ S.map (L.map δ) :=
    i.hom.naturality δ
  rw [rawComparison_hom_app, rawComparison_hom_app, ← Category.assoc, hn]
  have hs := congrArg (fun f ↦
    i.hom.app ((AdicCohomology.quotient J (n + 2)).obj M) ≫ S.map f)
    (sheafComparison_square T J U n M)
  simpa only [S, L, δ, i, comparisonRawRightAdjoint, Functor.comp_map,
    Functor.map_comp, Category.assoc, rawStep, NatTrans.comp_app,
    whiskerRight_app, Functor.associator_hom_app, Category.comp_id] using hs

end NormalizedRealization

section AdjointTransport
variable {B D E : Type*} [Category* B] [Category* D] [Category* E]
  {F : B ⥤ E} {R : E ⥤ B} {K : E ⥤ B}

private theorem rightTransformation_ext (a : F ⊣ R) (α β : R ⟶ K)
    (h : ∀ M, a.unit.app M ≫ α.app (F.obj M) =
      a.unit.app M ≫ β.app (F.obj M)) : α = β := by
  ext N
  calc
    α.app N = (a.unit.app (R.obj N) ≫ R.map (a.counit.app N)) ≫ α.app N := by
      simp only [a.right_triangle_components, Functor.id_obj, Category.id_comp]
    _ = (a.unit.app (R.obj N) ≫ α.app (F.obj (R.obj N))) ≫
        K.map (a.counit.app N) := by
      simpa only [Category.assoc, Functor.id_obj, Functor.comp_obj] using
        congrArg (fun f ↦ a.unit.app (R.obj N) ≫ f) (α.naturality (a.counit.app N))
    _ = (a.unit.app (R.obj N) ≫ β.app (F.obj (R.obj N))) ≫
        K.map (a.counit.app N) := by rw [h]
    _ = β.app N := by
      rw [Category.assoc, ← β.naturality, ← Category.assoc,
        a.right_triangle_components]
      simp only [Functor.id_obj, Category.id_comp]

private theorem successor_transport
    {F₀ : B ⥤ D} {R₀ S₀ : D ⥤ B} {F₁ : B ⥤ E} {R₁ S₁ : E ⥤ B}
    (a₀ : F₀ ⊣ R₀) (a₁ : F₁ ⊣ R₁) (b₀ : F₀ ⊣ S₀) (b₁ : F₁ ⊣ S₁)
    (C : E ⥤ D) (θ : F₁ ⋙ C ≅ F₀)
    (κ : R₁ ⟶ C ⋙ R₀) (κ' : S₁ ⟶ C ⋙ S₀)
    (ha : ∀ M, a₀.unit.app M = a₁.unit.app M ≫ κ.app (F₁.obj M) ≫
      R₀.map (θ.hom.app M))
    (hb : ∀ M, b₀.unit.app M = b₁.unit.app M ≫ κ'.app (F₁.obj M) ≫
      S₀.map (θ.hom.app M)) :
    (a₁.rightAdjointUniq b₁).hom ≫ κ' =
      κ ≫ whiskerLeft C (a₀.rightAdjointUniq b₀).hom := by
  apply rightTransformation_ext a₁
  intro M
  apply (cancel_mono (S₀.map (θ.hom.app M))).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, ← Category.assoc]
  rw [Adjunction.unit_rightAdjointUniq_hom_app, Category.assoc, ← hb]
  have hn := (a₀.rightAdjointUniq b₀).hom.naturality (θ.hom.app M)
  simp only [Functor.comp_obj] at hn
  calc
    b₀.unit.app M = a₀.unit.app M ≫
        (a₀.rightAdjointUniq b₀).hom.app (F₀.obj M) :=
      (Adjunction.unit_rightAdjointUniq_hom_app a₀ b₀ M).symm
    _ = (a₁.unit.app M ≫ κ.app (F₁.obj M)) ≫
        (R₀.map (θ.hom.app M) ≫ (a₀.rightAdjointUniq b₀).hom.app (F₀.obj M)) := by
      rw [ha]
      simp only [Category.assoc]
    _ = _ := by rw [hn]; simp only [Category.assoc]

private theorem compare_rightAdjointUniq_square
    {F₀ : B ⥤ D} {R₀ S₀ : D ⥤ B} {F₁ : B ⥤ E} {R₁ S₁ : E ⥤ B}
    {P₀ P₁ : B ⥤ B}
    (a₀ : F₀ ⊣ R₀) (a₁ : F₁ ⊣ R₁) (b₀ : F₀ ⊣ S₀) (b₁ : F₁ ⊣ S₁)
    (C : E ⥤ D) (θ : F₁ ⋙ C ≅ F₀)
    (κ : R₁ ⟶ C ⋙ R₀) (κ' : S₁ ⟶ C ⋙ S₀)
    (e₀ : P₀ ≅ F₀ ⋙ R₀) (e₁ : P₁ ≅ F₁ ⋙ R₁) (δ : P₁ ⟶ P₀)
    (ha : ∀ M, a₀.unit.app M = a₁.unit.app M ≫ κ.app (F₁.obj M) ≫
      R₀.map (θ.hom.app M))
    (hb : ∀ M, b₀.unit.app M = b₁.unit.app M ≫ κ'.app (F₁.obj M) ≫
      S₀.map (θ.hom.app M))
    (he : ∀ M, δ.app M ≫ e₀.hom.app M =
      e₁.hom.app M ≫ κ.app (F₁.obj M) ≫ R₀.map (θ.hom.app M)) (M : B) :
    δ.app M ≫ (e₀ ≪≫ isoWhiskerLeft F₀ (a₀.rightAdjointUniq b₀)).hom.app M =
      (e₁ ≪≫ isoWhiskerLeft F₁ (a₁.rightAdjointUniq b₁)).hom.app M ≫
        κ'.app (F₁.obj M) ≫ S₀.map (θ.hom.app M) := by
  let t₀ := a₀.rightAdjointUniq b₀
  have ht := congr_app (successor_transport a₀ a₁ b₀ b₁ C θ κ κ' ha hb) (F₁.obj M)
  simp only [NatTrans.comp_app, whiskerLeft_app] at ht
  have hn := t₀.hom.naturality (θ.hom.app M)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    whiskerLeft_app]
  calc
    _ = (e₁.hom.app M ≫ κ.app (F₁.obj M) ≫ R₀.map (θ.hom.app M)) ≫
        t₀.hom.app (F₀.obj M) := by rw [← Category.assoc, he]
    _ = e₁.hom.app M ≫ κ.app (F₁.obj M) ≫
        t₀.hom.app (C.obj (F₁.obj M)) ≫ S₀.map (θ.hom.app M) := by
      simpa only [Category.assoc, Functor.comp_obj] using
        congrArg (fun f ↦ e₁.hom.app M ≫ κ.app (F₁.obj M) ≫ f) hn
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ e₁.hom.app M ≫ f ≫ S₀.map (θ.hom.app M)) ht.symm

end AdjointTransport

attribute [local irreducible] adicPerfectQuotientFunctor

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The tensor-quotient identification on constant sections respects scalar transitions.
The right adjoints and the successor mates here are the already constructed ones;
this statement neither constructs an adjunction nor asserts a unit equation.
Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK; proetale.tex,
Tag 09C6, the ordinary constant finite-quotient tensor calculation.
(auxiliary; not a blueprint node).

Proof: write T for the coefficient site and L for constant module realization on
its slice. Reassociate scalar extension and commute it with slice restriction.
The completion cone equation identifies the composite coefficient map with
A -> A/J^(n+1). The generator-normalized constant scalar comparison
moduleComparison_tensor identifies this direct scalar extension with the constant
quotient-ring realization of (A/J^(n+1)) tensor_A M. The algebraic equivalence
quotTensorEquivQuotSMul identifies that tensor product with M/J^(n+1)M,
naturally in M. Restrict scalars to A and use sectionsIso to identify ordinary
constant module sections with L followed by terminal sections. Invert these
comparisons to obtain e for the normalized tensor/sections adjunction.

The scalar-extension unit inserts 1 in a tensor. The balancing map multiplies
successive scalar factors. Consequently both successor composites on a constant
quotient class of m send it to the class of 1 tensor m at the lower level.
This is equality of morphisms of constant module sheaves before taking sections:
constant presheaf generators determine a sheaf morphism by the sheafification
universal property. Naturality extends the generator calculation through the
constant scalar comparison and the algebraic tensor-quotient equivalence.
Evaluation at the terminal slice object gives the displayed equation on all
sections, including sections which are only locally constant.

Finally sectionModel_exists constructs an adjunction tower from these concrete
sections functors, and sectionModel selects from this completely proved theorem.
For the selected right adjoints use the unique right-adjoint isomorphisms t_n
from the normalized sections adjoints, characterized by eta_can followed by
t_n(F_n M) equalling the selected unit. Replace e_can,n by e_can,n followed by
t_n(F_n M). The selected successor map is the mate of inverse balancing:
the stored unit identity characterizes that mate uniquely. Indeed, precompose
naturality at the upper counit by the upper unit and use the right triangle
identity to recover every component from this unit identity. Thus it is t_(n+1)
inverse, followed by the normalized mate, followed by C_n(t_n). Naturality of t_n
with respect to theta_n cancels the adjacent inverse factors and gives the
displayed equation with exactly AdicQuotientSections.step. No choice of a witness
of this theorem is used to define an object. The calculation remains valid for
zero modules, the zero ring, J = 0 and J = top; all maps then have their usual
quotient or zero interpretations. -/
theorem adicPerfectQuotientSectionComparison (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    let G := AdicCohomology.sections
      ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U))
    ∃ (e : ∀ n : ℕ, AdicCohomology.quotient J (n + 1) ⋙ G ≅
        adicPerfectQuotientFunctor X J U n ⋙ AdicQuotientSections.rightAdjoint X J U n),
      ∀ (n : ℕ) (M : ModuleCat.{max v (u + 1)} A),
        G.map ((AdicCohomology.transition J
          (Nat.add_le_add_right (Nat.le_succ n) 1)).app M) ≫ (e n).hom.app M =
          (e (n + 1)).hom.app M ≫
            (AdicQuotientSections.step X J U n).app
              ((adicPerfectQuotientFunctor X J U (n + 1)).obj M) ≫
            (AdicQuotientSections.rightAdjoint X J U n).map
              ((adicPerfectQuotientModuleStep X J U n).hom.app M) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let F := fun n ↦ adicPerfectQuotientFunctor X J U n
  let R := fun n ↦ AdicQuotientSections.rawRightAdjoint X J U n
  let a : ∀ n, F n ⊣ R n := fun n ↦ by
    dsimp only [F, R]
    unfold adicPerfectQuotientFunctor adicPerfectLocalFunctor
    exact normalizedAdjunction T J U n
  let e₀ : ∀ n, AdicCohomology.quotient J (n + 1) ⋙
      AdicCohomology.sections (T.over U) (Over.mk (𝟙 U)) ≅ F n ⋙ R n := fun n ↦ by
    dsimp only [F, R]
    unfold adicPerfectQuotientFunctor adicPerfectLocalFunctor
    exact rawComparison T J U n
  let b := AdicQuotientSections.adjunction X J U
  let t := fun n ↦ (a n).rightAdjointUniq (b n)
  refine ⟨fun n ↦ e₀ n ≪≫ isoWhiskerLeft (F n) (t n), ?_⟩
  intro n M
  let θ := adicPerfectQuotientModuleStep X J U n
  let C := change (adicPerfectQuotientScalarStep X J U n)
  let θ' : F (n + 1) ⋙ C ≅ F n := by
    dsimp only [F, C]
    unfold adicPerfectQuotientFunctor adicPerfectLocalFunctor
    exact comparisonModuleStep T J U n
  have hθ : θ = θ' := by
    unfold θ θ' adicPerfectQuotientModuleStep comparisonModuleStep functorScalarCompIso
      associatorWhisker
    dsimp only [F, C]
    unfold adicPerfectQuotientFunctor
    dsimp only [T, adicPerfectLocalFunctor, comparisonQuotientFunctor, comparisonLocalFunctor,
      modelPresentationFunctor, adicResidueLocalProjection, adicPerfectQuotientScalarStep,
      comparisonProjection, comparisonScalarStep, _root_.id]
    simp only [Functor.assoc]
  refine compare_rightAdjointUniq_square (a n) (a (n + 1)) (b n) (b (n + 1)) C θ
    (rawStep T J U n) (AdicQuotientSections.step X J U n) (e₀ n) (e₀ (n + 1))
    (whiskerRight (AdicCohomology.transition J
      (Nat.add_le_add_right (Nat.le_succ n) 1))
      (AdicCohomology.sections (T.over U) (Over.mk (𝟙 U)))) ?_
    (AdicQuotientSections.step_unit X J U n) ?_ M
  · intro N
    rw [hθ]
    dsimp only [a, θ', F, R, C]
    unfold adicPerfectQuotientFunctor adicPerfectLocalFunctor
    exact rawStep_unit T J U n N
  · intro N
    rw [hθ]
    dsimp only [e₀, θ', F, R, C]
    unfold adicPerfectQuotientFunctor adicPerfectLocalFunctor
    exact rawComparison_square T J U n N

end AlgebraicGeometry.Scheme
