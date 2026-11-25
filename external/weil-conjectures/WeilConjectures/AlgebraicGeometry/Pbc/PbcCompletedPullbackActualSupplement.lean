/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedCechComparison
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual

/-! # Completed pullback on the completed-coefficient categories

The coefficient structure is fixed on all quotient projections. Ordinary pullback
is its total derived sheafified tensor inverse image. Completion is characterized
by its reflection universal property on the actual intrinsic complete subcategory.

## References

* Tag 099N (2), (5)
* Stacks 03D2 and 099N
* Stacks Project, Tag 03D7
* Stacks Project, Tag 099N, (2) and (5), and Tags 099B and 0A0E
* Stacks Project, Tag 099N, (2) and (5)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
private theorem commShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

-- The comparison determines the shift structure by Kan uniqueness, degree by degree.
private theorem rightKanShift_unique
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ]
    {E : Type*} [Category* E] [HasShift E ℤ]
    (F : C ⥤ E) [F.CommShift ℤ] (Q : C ⥤ D) [Q.CommShift ℤ]
    (LF : D ⥤ E) (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α]
    (s t : LF.CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift α ℤ)
    (ht : letI := t; NatTrans.CommShift α ℤ) : s = t := by
  have square (q : LF.CommShift ℤ) (hq : letI := q; NatTrans.CommShift α ℤ)
      (n : ℤ) (X : C) :
      LF.map ((Q.commShiftIso n).hom.app X) ≫
          (Functor.commShiftIso LF (self := q) n).hom.app (Q.obj X) ≫
            (shiftFunctor E n).map (α.app X) =
        α.app ((shiftFunctor C n).obj X) ≫ (F.commShiftIso n).hom.app X := by
    let := q
    have := hq
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm α n X
  have he (n : ℤ) : Functor.commShiftIso LF (self := s) n =
      Functor.commShiftIso LF (self := t) n := by
    let H := shiftFunctor E n
    let P := Functor.RightExtension.postcompose₂ Q F H
    let : IsIso (𝟙 (F ⋙ H)) := inferInstance
    let : P.IsEquivalence := by
      dsimp [P, Functor.RightExtension.postcompose₂]
      let a : ((Functor.whiskeringRight D E E).obj H) ⋙
          (Functor.whiskeringLeft C D E).obj Q ⟶
          (Functor.whiskeringLeft C D E).obj Q ⋙
            ((Functor.whiskeringRight C E E).obj H) :=
        { app G := (Functor.associator Q G H).inv }
      let : IsIso a := by apply NatIso.isIso_of_isIso_app
      exact CostructuredArrow.isEquivalenceMap₂ a (𝟙 _)
    let γ := (Functor.associator Q LF H).inv ≫ whiskerRight α H
    have : (LF ⋙ H).IsRightKanExtension γ := by
      constructor
      refine ⟨IsTerminal.ofIso
        (IsTerminal.isTerminalObj P _ (LF.isUniversalOfIsRightKanExtension α)) ?_⟩
      exact Functor.RightExtension.postcompose₂ObjMkIso H α
    apply Iso.ext
    apply (LF ⋙ H).hom_ext_of_isRightKanExtension γ
    ext X
    simp only [γ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]
    apply (cancel_epi (LF.map ((Q.commShiftIso n).hom.app X))).1
    simpa only [Category.assoc] using (square s hs n X).trans (square t ht n X).symm
  exact commShift_ext s t he

-- Transport the unit along the K-injective equivalence, then detect it on resolutions.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem actualRightDerivedUnitShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have hE : E.CommShift ℤ := by infer_instance
  have hU : NatTrans.CommShift E.unitIso.hom ℤ := by infer_instance
  have heq : whiskerLeft inj F.rightDerivedFunctorUnit =
      (leftUnitor G).inv ≫ whiskerRight E.unitIso.hom G ≫
        (associator E.functor E.inverse G).hom ≫
        whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, leftUnitor_inv_app, Category.id_comp, hinv]
    simp only [Category.assoc]
    erw [Category.id_comp, Category.comp_id]
    have h := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    dsimp only [Functor.comp_map, Functor.comp_obj] at h
    change _ = (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      (inj.map (E.unit.app X)) ≫ _
    erw [reassoc_of% h]
    rw [← CategoryTheory.Functor.map_comp]
    change _ = _ ≫ F.rightDerivedFunctor.map
      (E.functor.map (E.unit.app X) ≫ E.counit.app (E.functor.obj X))
    erw [E.functor_unit_comp]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have : NatTrans.CommShift (whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨I, hI, i, hi, _⟩ := CategoryTheory.Abelian.HasKInjectiveResolutions.exists_isKInjective P
  have := hI
  have := hi
  refine ⟨HomotopyCategory.KInjectives.mk I,
    (HomotopyCategory.quotient C (.up ℤ)).map i, ?_⟩
  change IsIso (F.rightDerivedFunctor.map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map i)))
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map i)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) i).2 (by infer_instance)
  infer_instance

namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The sectionwise module direct image. -/
abbrev pbcActualModulePush := completedModuleDirectImage g d

/-- The module inverse image followed by completed scalar tensor. -/
abbrev pbcActualModulePull := completedModulePullback g d

attribute [-instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModelUp_isContinuous in
/-- The ordinary tensor-unit section uses the actual model-site inverse-image unit. -/
def pbcActualModuleUnitSection (M : pbcModules Y (pbcAdicCompletion Y d))
    (U : Y.ProEt) (x : M.val.obj (op U)) :
    ((pbcActualModulePush g d).obj ((pbcActualModulePull g d).obj M)).val.obj (op U) :=
  reductionTensorSection X (completedCoefficientMap g d)
    ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M)
    (op ((proEtaleBaseChange g).obj U)) 1
    (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1} (proEtaleModelRingUnit g
      (pbcAdicCompletion Y d))).unit.app
        ((proEtaleModuleToModel ((adicLisseForget Y).obj (pbcAdicCompletion Y d))).obj M)).val.app
          (op (AsSmall.up.obj U)) x)

/-- The pullback and direct image have the uniquely normalized tensor adjunction. -/
theorem pbcActualModuleAdjunction_exists :
    ∃! adj : pbcActualModulePull g d ⊣ pbcActualModulePush g d,
      ∀ (M : pbcModules Y (pbcAdicCompletion Y d)) (U : Y.ProEt) (x : M.val.obj (op U)),
        (adj.unit.app M).val.app (op U) x = pbcActualModuleUnitSection g d M U x := by
  let : (proEtaleModelBaseChange g).IsContinuous
      (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
    proEtaleModelBaseChange_isContinuous g
  let : (AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).IsContinuous
      (ProEt.topology Y) (proEtaleModelTopology Y) := proEtaleModelUp_isContinuous Y
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsContinuous
      (ProEt.topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  let R := pbcAdicCompletion Y d
  let φ := completedCoefficientMap g d
  obtain ⟨adjS, hadjS⟩ :=
    SheafOfModules.ScalarReductionProof.tensorAdjunction_of_identifications φ
      (reductionChange X φ) (reductionChangeExistence X φ).choose_spec.choose
      (reductionChangeExistence X φ).choose_spec.choose_spec.choose
  let adj := (canonicalAdjunction g R).comp adjS
  let e : SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ) ⋙
      AlgebraicGeometry.Scheme.T g R ≅
      pbcActualModulePush g d := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl)
    · intro M N a
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      rfl
  let a : pbcActualModulePull g d ⊣ pbcActualModulePush g d := adj.ofNatIsoRight e
  have ha : ∀ (M : pbcModules Y (pbcAdicCompletion Y d)) (U : Y.ProEt)
      (x : M.val.obj (op U)),
      (a.unit.app M).val.app (op U) x = pbcActualModuleUnitSection g d M U x := by
    intro M U x
    change ((adjS.unit.app ((proEtaleModuleInverseImage g R).obj M)).val.app
      (op ((proEtaleBaseChange g).obj U))
        (((canonicalAdjunction g R).unit.app M).val.app (op U) x)) = _
    rw [canonicalUnit_sections, hadjS]
    rfl
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  ext U x
  exact (ha' M U.unop x).trans (ha M U.unop x).symm

/-- The actual module adjunction, with the inverse-image tensor unit retained. -/
def pbcActualModuleAdjunction := (pbcActualModuleAdjunction_exists g d).exists.choose

/-- Pullback and pushforward are additive. -/
theorem pbcActualModuleOperations_additive :
    (pbcActualModulePull g d).Additive ∧ (pbcActualModulePush g d).Additive := by
  exact ⟨completedModulePullback_additive g d, completedModuleDirectImage_additive g d⟩

/-- Additivity of the specified module pullback. -/
instance pbcActualModulePull_additive : (pbcActualModulePull g d).Additive :=
  (pbcActualModuleOperations_additive g d).1

/-- Additivity of the specified module direct image. -/
instance pbcActualModulePush_additive : (pbcActualModulePush g d).Additive :=
  (pbcActualModuleOperations_additive g d).2

/-- The ordinary total derived pullback with its fixed resolving pair. -/
abbrev pbcActualDerivedPull := completedOrdinaryPullback g d

/-- The universal ordinary-pullback counit. -/
abbrev pbcActualPullCounit := completedOrdinaryPullbackCounit g d

/-- Its computation on cochain representatives retains the universal counit. -/
def pbcActualPullComplexCounit (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (pbcActualDerivedPull g d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((pbcActualModulePull g d).mapHomologicalComplex (.up ℤ)).obj P) :=
  (pbcActualDerivedPull g d).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (pbcActualPullCounit g d).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((pbcActualModulePull g d).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((pbcActualModulePull g d).mapHomologicalComplex (.up ℤ)).obj P)

/-- Ordinary derived direct image, computed using K-injectives in all modules. -/
abbrev pbcActualDerivedPush : PbcCompletedDerived X d ⥤ PbcCompletedDerived Y d :=
  completedDerivedDirectImage g d

/-- The universal homotopy-category unit of ordinary derived direct image. -/
def pbcActualPushUnit :
    (pbcActualModulePush g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ pbcActualDerivedPush g d :=
  (pbcActualModulePush g d).rightDerivedFunctorUnit

/-- Universality of the named ordinary left derived pair. -/
@[instance] theorem pbcActualPullUniversal :
    (pbcActualDerivedPull g d).IsLeftDerivedFunctor (pbcActualPullCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  unfold pbcActualDerivedPull completedOrdinaryPullback pbcActualPullCounit
    completedOrdinaryPullbackCounit
  exact (completedOrdinaryPullback_exists g d).choose_spec.choose_spec.1

/-- Universality of the named ordinary right derived pair. -/
@[instance] theorem pbcActualDirectUniversal :
    (pbcActualDerivedPush g d).IsRightDerivedFunctor
      (pbcActualPushUnit g d)
        (HomotopyCategory.quasiIso (pbcModules X (pbcAdicCompletion X d)) (.up ℤ)) := by
  dsimp [pbcActualDerivedPush, pbcActualPushUnit]
  infer_instance

-- `moduleBinaryBiproducts` has a free universe and leaves a stuck universe constraint here.
attribute [-instance] CategoryTheory.SignedDoubleHomCone.moduleBinaryBiproducts in
/-- The resolving left derived pair remains universal after the indicated direct image. -/
@[instance] theorem pbcActualDerivedLeftComposite :
    (pbcActualDerivedPull g d ⋙ pbcActualDerivedPush g d).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight (pbcActualPullCounit g d) (pbcActualDerivedPush g d))
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} Y
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1} _
  let C := pbcModules Y (pbcAdicCompletion Y d)
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let B := ((pbcActualModulePull g d).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh) ⋙ pbcActualDerivedPush g d
  let L := pbcActualDerivedPull g d ⋙ pbcActualDerivedPush g d
  let α : DerivedCategory.Qh ⋙ L ⟶ B :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight (pbcActualPullCounit g d) (pbcActualDerivedPush g d)
  let P : Set (HomotopyCategory C (.up ℤ)) :=
    { Z | IsIso ((pbcActualPullCounit g d).app Z) }
  have hres (Z : HomotopyCategory C (.up ℤ)) :
      ∃ (Z' : HomotopyCategory C (.up ℤ)) (s : Z' ⟶ Z), Z' ∈ P ∧ W s := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
    obtain ⟨K', s, hK', _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) (R := pbcAdicCompletion Y d) K
    refine ⟨_, (HomotopyCategory.quotient C (.up ℤ)).map s, ?_,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
    change IsIso ((pbcActualPullCounit g d).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K'))
    unfold pbcActualPullCounit completedOrdinaryPullbackCounit completedOrdinaryPullback
    exact (completedOrdinaryPullback_exists g d).choose_spec.choose_spec.2 K' hK'
  have hcompute (Z : HomotopyCategory C (.up ℤ)) (hZ : Z ∈ P) : IsIso (α.app Z) := by
    have : IsIso ((pbcActualPullCounit g d).app Z) := hZ
    change IsIso (𝟙 _ ≫ (pbcActualDerivedPush g d).map
      ((pbcActualPullCounit g d).app Z))
    rw [Category.id_comp]
    infer_instance
  have hinv (Z Z' : HomotopyCategory C (.up ℤ)) (s : Z ⟶ Z')
      (hZ : Z ∈ P) (hZ' : Z' ∈ P) (hs : W s) : IsIso (B.map s) := by
    have := hcompute Z hZ
    have := hcompute Z' hZ'
    have : IsIso (DerivedCategory.Qh.map s) :=
      Localization.inverts DerivedCategory.Qh W s hs
    have heq : B.map s = inv (α.app Z) ≫ L.map (DerivedCategory.Qh.map s) ≫ α.app Z' := by
      apply (cancel_epi (α.app Z)).1
      simpa only [Functor.comp_map, Category.assoc, IsIso.hom_inv_id_assoc] using
        (α.naturality s).symm
    rw [heq]
    infer_instance
  obtain ⟨_, L', ε, hL', _, hε⟩ :=
    Functor.leftDerived_from_resolvingClass C (DerivedCategory (pbcModules Y
      (pbcAdicCompletion Y d))) B P hres hinv
  have := hL'
  let δ := L'.leftDerivedLift ε W L α
  have hδ (Z : HomotopyCategory C (.up ℤ)) (hZ : Z ∈ P) :
      IsIso (δ.app (DerivedCategory.Qh.obj Z)) := by
    have := hε Z hZ
    have := hcompute Z hZ
    have heq : δ.app (DerivedCategory.Qh.obj Z) = α.app Z ≫ inv (ε.app Z) := by
      apply (cancel_mono (ε.app Z)).1
      simp [δ]
    rw [heq]
    infer_instance
  have : IsIso δ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    have := Localization.essSurj (DerivedCategory.Qh (C := C)) W
    let Z := (DerivedCategory.Qh (C := C)).objPreimage K
    obtain ⟨Z', s, hZ', hs⟩ := hres Z
    have : IsIso (DerivedCategory.Qh.map s) :=
      Localization.inverts DerivedCategory.Qh W s hs
    let e : DerivedCategory.Qh.obj Z' ≅ K := asIso (DerivedCategory.Qh.map s) ≪≫
      (DerivedCategory.Qh (C := C)).objObjPreimageIso K
    exact (NatTrans.isIso_app_iff_of_iso δ e).1 (hδ Z' hZ')
  exact (L'.isLeftDerivedFunctor_iff_isIso_leftDerivedLift ε W L α).2 this

/-- The resolving right derived pair remains universal after the indicated pullback. -/
@[instance] theorem pbcActualDerivedRightComposite :
    (pbcActualDerivedPush g d ⋙ pbcActualDerivedPull g d).IsRightDerivedFunctor
      (whiskerRight (pbcActualPushUnit g d) (pbcActualDerivedPull g d) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso (pbcModules X (pbcAdicCompletion X d)) (.up ℤ)) := by
  apply (HomotopyCategory.KInjectives.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso
  intro I
  obtain ⟨I, hI, rfl⟩ := I.mk_surjective
  have : I.IsKInjective := hI
  have : IsIso ((pbcActualModulePush g d).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ _).obj I)) := inferInstance
  change IsIso ((pbcActualDerivedPull g d).map
    ((pbcActualModulePush g d).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I)) ≫ 𝟙 _)
  infer_instance

/-- The derived adjunction obtained from the actual module adjunction and its
universal derived counit/unit. -/
def pbcActualDerivedAdjunction :
    pbcActualDerivedPull g d ⊣ pbcActualDerivedPush g d :=
  (pbcActualModuleAdjunction g d).mapHomotopyCategory (.up ℤ) |>.derived
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
      (HomotopyCategory.quasiIso (pbcModules X (pbcAdicCompletion X d)) (.up ℤ))
      (pbcActualPullCounit g d) (pbcActualPushUnit g d)

set_option linter.unusedVariables false in
/-- The ordinary comparison on resolving complexes uniquely fixes the derived shift. -/
theorem pbcActualPullShift_exists :
    ∃! q : (pbcActualDerivedPull g d).CommShift ℤ,
      (fun [qInst : (pbcActualDerivedPull g d).CommShift ℤ] ↦
        NatTrans.CommShift (pbcActualPullCounit g d) ℤ) (qInst := q) := by
  have hkan := Functor.IsLeftDerivedFunctor.isRightKanExtension
    (pbcActualDerivedPull g d) (pbcActualPullCounit g d)
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
  have := hkan
  obtain ⟨q, hq⟩ := Functor.rightKanExtension_coherentShift _ DerivedCategory.Qh
    (pbcActualDerivedPull g d) (pbcActualPullCounit g d) hkan
  exact ⟨q, hq, fun q' hq' ↦ rightKanShift_unique _ _ _ _ q' q hq' hq⟩

/-- The canonical shift structure, normalized by the universal derived comparison. -/
instance pbcActualPullShift : (pbcActualDerivedPull g d).CommShift ℤ :=
  (pbcActualPullShift_exists g d).exists.choose

set_option linter.unusedVariables false in
/-- The ordinary comparison on resolving complexes uniquely fixes the derived shift. -/
theorem pbcActualPushShift_exists :
    ∃! q : (pbcActualDerivedPush g d).CommShift ℤ,
      (fun [qInst : (pbcActualDerivedPush g d).CommShift ℤ] ↦
        NatTrans.CommShift (pbcActualPushUnit g d) ℤ) (qInst := q) := by
  let F := pbcActualModulePush g d
  let q : (pbcActualDerivedPush g d).CommShift ℤ :=
    inferInstanceAs (F.rightDerivedFunctor.CommShift ℤ)
  have hq : (fun [qInst : (pbcActualDerivedPush g d).CommShift ℤ] ↦
      NatTrans.CommShift (pbcActualPushUnit g d) ℤ) (qInst := q) :=
    actualRightDerivedUnitShift F
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  have square (s : (pbcActualDerivedPush g d).CommShift ℤ)
      (hs : letI := s; NatTrans.CommShift (pbcActualPushUnit g d) ℤ)
      (n : ℤ) (I : HomotopyCategory (pbcModules X (pbcAdicCompletion X d)) (.up ℤ)) :
      (((pbcActualModulePush g d).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh).commShiftIso n).hom.app I ≫
          (shiftFunctor _ n).map ((pbcActualPushUnit g d).app I) =
        (pbcActualPushUnit g d).app (I⟦n⟧) ≫
          (pbcActualDerivedPush g d).map ((DerivedCategory.Qh.commShiftIso n).hom.app I) ≫
          (Functor.commShiftIso (pbcActualDerivedPush g d) (self := s) n).hom.app
            (DerivedCategory.Qh.obj I) := by
    let := s
    have := hs
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm (pbcActualPushUnit g d) n I
  have he (n : ℤ) : Functor.commShiftIso (pbcActualDerivedPush g d) (self := q') n =
      Functor.commShiftIso (pbcActualDerivedPush g d) (self := q) n := by
    apply Iso.ext
    ext K
    obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
    have := hI
    let e := e ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm
    have hi : ((Functor.commShiftIso (pbcActualDerivedPush g d) (self := q') n)).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) =
        ((Functor.commShiftIso (pbcActualDerivedPush g d) (self := q) n)).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) := by
      let Ih := (HomotopyCategory.quotient _ _).obj I
      have hshift : IsIso ((pbcActualPushUnit g d).app (Ih⟦n⟧)) := by
        apply (NatTrans.isIso_app_iff_of_iso (pbcActualPushUnit g d)
          (((HomotopyCategory.quotient _ _).commShiftIso n).app I)).1
        change IsIso (F.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj (I⟦n⟧)))
        infer_instance
      apply (cancel_epi ((pbcActualPushUnit g d).app (Ih⟦n⟧) ≫
        (pbcActualDerivedPush g d).map ((DerivedCategory.Qh.commShiftIso n).hom.app Ih))).1
      simpa only [Category.assoc] using
        (square q' hq' n Ih).symm.trans (square q hq n Ih)
    apply (cancel_mono ((pbcActualDerivedPush g d ⋙ shiftFunctor _ n).map e.hom)).1
    rw [← (Functor.commShiftIso (pbcActualDerivedPush g d) (self := q') n).hom.naturality,
      ← (Functor.commShiftIso (pbcActualDerivedPush g d) (self := q) n).hom.naturality]
    exact congrArg (fun a ↦ (shiftFunctor _ n ⋙ pbcActualDerivedPush g d).map e.hom ≫ a) hi
  exact commShift_ext _ _ he

/-- The canonical shift structure, normalized by the universal derived comparison. -/
instance pbcActualPushShift : (pbcActualDerivedPush g d).CommShift ℤ :=
  (pbcActualPushShift_exists g d).exists.choose

-- The two coefficient presentations have equivalent module and derived categories.
-- These transport arguments are the existing ones used by WeilTensorProduct.
section CompletionPresentation
variable (X)
variable (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

set_option backward.isDefEq.respectTransparency false in
private def wfRestrictId (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules X R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun U ↦ (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))) (fun _ ↦ by ext U x; rfl)

set_option backward.isDefEq.respectTransparency false in
private def wfPresentationBackEquiv :
    adicDatumModules X (intrinsicPresentationDatum d) ≌ pbcModules X (pbcAdicCompletion X d) :=
  CategoryTheory.Equivalence.mk (intrinsicPresentationModulesBack X d)
    (intrinsicPresentationModules X d)
    ((pbcRestrictComp (pbcCompletedComparison X d).hom (pbcCompletedComparison X d).inv
        (𝟙 _) (pbcCompletedComparison X d).hom_inv_id ≪≫
      wfRestrictId X _).symm)
    (intrinsicPresentationRoundTrip X d).symm

attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip wfRestrictId

set_option backward.isDefEq.respectTransparency false in
private theorem wfComplete_of_presentation
    (M : PbcCompletedDerived X d) (s : ℕ) (b : Fin s → A)
    (hb : Ideal.span (Set.range b) = d.ideal)
    (C : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ)
    (eC : (completedConstantQ _).obj C ≅
      (pbcDerivedExtend (pbcCompletedComparison X d).inv).obj M)
    (hC : IsCompletedIntrinsicallyDerivedComplete X (intrinsicPresentationDatum d)
      s b hb C eC) :
    WfIsComplete X d r a ha M := by
  let G := intrinsicPresentationModules X d
  let B := intrinsicPresentationModulesBack X d
  have : B.IsEquivalence := (wfPresentationBackEquiv X d).isEquivalence_functor
  let BD := B.mapDerivedCategory
  let GD := G.mapDerivedCategory
  have : BD.IsEquivalence := inferInstance
  have : (pbcDerivedRestrict (pbcCompletedComparison X d).inv).IsEquivalence :=
    inferInstanceAs BD.IsEquivalence
  let adj := pbcDerivedScalarAdjunction (pbcCompletedComparison X d).inv
  have : IsIso adj.unit := by dsimp [adj]; infer_instance
  let D := (B.mapHomologicalComplex (.up ℤ)).obj C
  let eD : DerivedCategory.Q.obj D ≅ M :=
    (B.mapDerivedCategoryFactors.app C).symm ≪≫ BD.mapIso eC ≪≫
      (asIso (adj.unit.app M)).symm
  let C' := (G.mapHomologicalComplex (.up ℤ)).obj D
  let j := (wfPresentationBackEquiv X d).unitIso
  let k : DerivedCategory.Q.obj C' ≅ DerivedCategory.Q.obj C :=
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex j (.up ℤ)).app C)).symm
  obtain ⟨F, η, hF⟩ := completedIntrinsicCompletion_descends X
    (intrinsicPresentationDatum d) s b
  obtain ⟨iC, hiC⟩ := hF C
  obtain ⟨iC', hiC'⟩ := hF C'
  have hu : IsIso ((completedConstantQ _).map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) s b C)) := by
    have : IsIso (eC.inv ≫ (completedConstantQ _).map
        (completedKoszulUnitComplex X (intrinsicPresentationDatum d) s b C)) := hC
    exact IsIso.of_isIso_comp_left eC.inv _
  have hη : IsIso (η.app (DerivedCategory.Q.obj C)) := by
    have : IsIso (η.app (DerivedCategory.Q.obj C) ≫ iC.hom) := by
      rw [hiC]
      exact hu
    exact IsIso.of_isIso_comp_right _ iC.hom
  have hη' : IsIso (η.app (DerivedCategory.Q.obj C')) := by
    have hn := η.naturality k.hom
    dsimp only [Functor.id_map] at hn
    have : IsIso (η.app (DerivedCategory.Q.obj C') ≫ F.map k.hom) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (F.map k.hom)
  have hu' : IsIso ((completedConstantQ _).map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) s b C')) := by
    rw [← hiC']
    infer_instance
  have hq : QuasiIso (completedKoszulUnitComplex X (intrinsicPresentationDatum d) s b C') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hu'
  let t : D ≅ (B.mapHomologicalComplex (.up ℤ)).obj C' :=
    (NatIso.mapHomologicalComplex (intrinsicPresentationRoundTrip X d) (.up ℤ)).app D
  have hcomp : intrinsicCompletionComplexUnit X d s b D =
      t.hom ≫ (B.mapHomologicalComplex (.up ℤ)).map
        (completedKoszulUnitComplex X (intrinsicPresentationDatum d) s b C') := by
    unfold intrinsicCompletionComplexUnit intrinsicCompletionUnitComponent
    ext q
    rfl
  have hDC : QuasiIso (intrinsicCompletionComplexUnit X d s b D) := by
    rw [hcomp]
    infer_instance
  have hQu : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d s b D)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hDC
  have hD : IsDerivedCompleteIntrinsic X d s b hb M D eD := by
    unfold IsDerivedCompleteIntrinsic intrinsicCompletionUnit intrinsicCompletion
    exact IsIso.comp_isIso' eD.isIso_inv hQu
  have : IsIso (intrinsicCompletionUnit X d s b hb M D eD) := hD
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison X d s b hb M D eD
  have hTower : d.TowerComplete X M := by
    change IsIso (d.completionUnit X M)
    change intrinsicCompletionUnit X d s b hb M D eD ≫ c.hom = d.completionUnit X M at hc
    rw [← hc]
    exact inferInstanceAs (IsIso (intrinsicCompletionUnit X d s b hb M D eD ≫ c.hom))
  exact (d.towerComplete_iff_intrinsic X M).1 hTower r a ha _ _

set_option backward.isDefEq.respectTransparency false in
private theorem wfPresentation_of_complete (M : PbcCompletedDerived X d)
    (hM : WfIsComplete X d r a ha M) : PbcIsIntrinsicallyComplete X d M := by
  let B := intrinsicPresentationModulesBack X d
  let G := intrinsicPresentationModules X d
  let E := wfPresentationBackEquiv X d
  have : B.IsEquivalence := E.isEquivalence_functor
  have : G.IsEquivalence := E.isEquivalence_inverse
  let C := wfCompletionRepresentative X d M
  let C' := (G.mapHomologicalComplex (.up ℤ)).obj C
  let real := DerivedCategory.Q.objObjPreimageIso M
  let adj := pbcDerivedScalarAdjunction (pbcCompletedComparison X d).inv
  have : E.symm.functor.Additive := inferInstanceAs G.Additive
  have : E.symm.inverse.Additive := inferInstanceAs B.Additive
  let ej := E.symm.mapDerivedCategory.toAdjunction
  let j : G.mapDerivedCategory ≅ pbcDerivedExtend (pbcCompletedComparison X d).inv :=
    Adjunction.leftAdjointUniq ej adj
  let eC := (G.mapDerivedCategoryFactors.app C).symm ≪≫
    G.mapDerivedCategory.mapIso real ≪≫ j.app M
  have hu : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) := by
    have : IsIso (real.inv ≫ DerivedCategory.Q.map
      (intrinsicCompletionComplexUnit X d r a C)) := by
      unfold WfIsComplete IsDerivedCompleteIntrinsic intrinsicCompletionUnit
        intrinsicCompletion at hM
      exact hM
    exact IsIso.of_isIso_comp_left real.inv _
  have hq : QuasiIso (intrinsicCompletionComplexUnit X d r a C) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hu
  let t : C ≅ (B.mapHomologicalComplex (.up ℤ)).obj C' :=
    (NatIso.mapHomologicalComplex (intrinsicPresentationRoundTrip X d) (.up ℤ)).app C
  have hcomp : intrinsicCompletionComplexUnit X d r a C =
      t.hom ≫ (B.mapHomologicalComplex (.up ℤ)).map
        (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C') := by
    unfold intrinsicCompletionComplexUnit intrinsicCompletionUnitComponent
    ext q
    rfl
  have hBu : QuasiIso ((B.mapHomologicalComplex (.up ℤ)).map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C')) := by
    have : QuasiIso (t.hom ≫ (B.mapHomologicalComplex (.up ℤ)).map
        (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C')) := by
      rw [← hcomp]
      exact hq
    exact quasiIso_of_comp_left t.hom _
  have hCu : QuasiIso (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C') :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ B).1 hBu
  refine ⟨r, a, ha, C', eC, ?_⟩
  change IsIso (eC.inv ≫ (completedConstantQ _).map
    (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C'))
  infer_instance

attribute [local irreducible] intrinsicCompletionComplex

private theorem wfComplete_iff_presentation (M : PbcCompletedDerived X d) :
    WfIsComplete X d r a ha M ↔ PbcIsIntrinsicallyComplete X d M := by
  constructor
  · exact wfPresentation_of_complete X d r a ha M
  · rintro ⟨s, b, hb, C, eC, hC⟩
    exact wfComplete_of_presentation X d r a ha M s b hb C eC hC

private theorem actualComplete_iso {M N : PbcCompletedDerived X d} (k : M ≅ N) :
    PbcIsIntrinsicallyComplete X d M ↔ PbcIsIntrinsicallyComplete X d N := by
  have h {M N : PbcCompletedDerived X d} (k : M ≅ N)
      (hM : PbcIsIntrinsicallyComplete X d M) : PbcIsIntrinsicallyComplete X d N := by
    obtain ⟨s, b, hb, C, eC, hC⟩ := hM
    refine ⟨s, b, hb, C,
      eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison X d).inv).mapIso k, ?_⟩
    change IsIso (eC.inv ≫ _) at hC
    have hu := (isIso_comp_left_iff eC.inv _).mp hC
    change IsIso ((_ ≫ eC.inv) ≫ _)
    infer_instance
  exact ⟨h k, h k.symm⟩

-- The Cech functor has the same essential image as the Koszul reflection.
-- Its shift isomorphism therefore supplies shift closure without expanding the fiber.
private theorem actualComplete_shift (M : PbcCompletedDerived X d)
    (hM : PbcIsIntrinsicallyComplete X d M) (n : ℤ) :
    PbcIsIntrinsicallyComplete X d (M⟦n⟧) := by
  classical
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let O := completedCechRing X d
  let E := completedCechDerivedEquiv X d
  let F := ringedCechCompletionFunctor O
    (ringedExtendedCech O r (fun i ↦ completedCechScalar X d (a i))).1
  have hE : E.functor.CommShift ℤ := by
    change ((completedCechModulesEquiv X d).functor.mapDerivedCategory).CommShift ℤ
    infer_instance
  obtain ⟨sF, _⟩ := (ringedInternalHom_exact (completedCechTopology X) O).1
    (DerivedCategory.Q.obj
      (ringedExtendedCech O r (fun i ↦ completedCechScalar X d (a i))).1)
  let : F.CommShift ℤ := sF
  have e (N : PbcCompletedDerived X d) :
      Nonempty (E.functor.obj (wfCompletionObj X d r a ha N) ≅ F.obj (E.functor.obj N)) := by
    let C := wfCompletionRepresentative X d N
    let real := DerivedCategory.Q.objObjPreimageIso N
    obtain ⟨e, _⟩ := completed_fiber_cech_comparison X d r a C
    exact ⟨e ≪≫ F.mapIso (E.functor.mapIso real)⟩
  have : IsIso (wfCompletionUnit X d r a ha M) :=
    (wfComplete_iff_presentation X d r a ha M).mpr hM
  let j : E.functor.obj M ≅ F.obj (E.functor.obj M) :=
    E.functor.mapIso (asIso (wfCompletionUnit X d r a ha M)) ≪≫ (e M).some
  let k : E.functor.obj (M⟦n⟧) ≅
      E.functor.obj (wfCompletionObj X d r a ha (M⟦n⟧)) :=
    (E.functor.commShiftIso n).app M ≪≫ (shiftFunctor _ n).mapIso j ≪≫
      ((F.commShiftIso n).app (E.functor.obj M)).symm ≪≫
      F.mapIso ((E.functor.commShiftIso n).app M).symm ≪≫ (e (M⟦n⟧)).some.symm
  apply (actualComplete_iso X d (E.functor.preimageIso k)).mpr
  exact (wfComplete_iff_presentation X d r a ha _).mp
    ((wfCompletionReflector X d r a ha).1 _)

end CompletionPresentation

variable (T : Scheme.{u})

/-- The intrinsic complete subcategory is reflective, with the Koszul completion unit. -/
@[instance] theorem pbcActualCompleteInclusion_isRightAdjoint :
    (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d)).IsRightAdjoint := by
  classical
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let P : ObjectProperty (PbcCompletedDerived T d) := PbcIsIntrinsicallyComplete T d
  let W := wfCompletion T d r a ha
  let L : PbcCompletedDerived T d ⥤ P.FullSubcategory :=
    P.lift (W ⋙ ObjectProperty.ι _) (fun M ↦
      (wfComplete_iff_presentation T d r a ha _).mp (W.obj M).property)
  let e (M : PbcCompletedDerived T d) (N : P.FullSubcategory) :
      (L.obj M ⟶ N) ≃ (M ⟶ N.obj) :=
    (ObjectProperty.fullyFaithfulι P).homEquiv.trans
      (Equiv.ofBijective _ ((wfCompletionReflector T d r a ha).2 M N.obj
        ((wfComplete_iff_presentation T d r a ha N.obj).mpr N.property)))
  let adj : L ⊣ P.ι := Adjunction.mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro M M' N f h
        apply (e M N).injective
        symm
        change wfCompletionUnit T d r a ha M ≫
          (L.map f ≫ (e M' N).symm h).hom = _
        dsimp only [ObjectProperty.FullSubcategory.comp_hom]
        rw [← Category.assoc]
        have hn : wfCompletionUnit T d r a ha M ≫ (L.map f).hom =
            f ≫ wfCompletionUnit T d r a ha M' := by
          exact (Equiv.ofBijective _ ((wfCompletionReflector T d r a ha).2 M
            (wfCompletionObj T d r a ha M')
            ((wfCompletionReflector T d r a ha).1 M'))).apply_symm_apply _
        rw [hn, Category.assoc]
        change f ≫ (e M' N) ((e M' N).symm h) = (e M N) ((e M N).symm (f ≫ h))
        simp
      homEquiv_naturality_right := by
        intro M N N' h f
        change wfCompletionUnit T d r a ha M ≫ (h ≫ f).hom =
          (wfCompletionUnit T d r a ha M ≫ h.hom) ≫ f.hom
        exact (Category.assoc _ _ _).symm }
  exact ⟨L, ⟨adj⟩⟩

/-- The canonical reflection onto the actual intrinsically complete subcategory.
Its defining universal property determines its objects up to the equality used
here, namely unique unit-compatible isomorphism. -/
def pbcActualCompletion : PbcCompletedDerived T d ⥤ PbcCompletedDerived T d :=
  (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d)).leftAdjoint ⋙
    (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d))

/-- The universal completion unit of the actual intrinsic complete subcategory. -/
def pbcActualCompletionUnit : 𝟭 (PbcCompletedDerived T d) ⟶ pbcActualCompletion d T :=
  (Adjunction.ofIsRightAdjoint (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d))).unit

/-- Ordinary derived pullback followed by the unit-normalized completion reflector.
This is equivalently the derived limit of the pulled-back strict reduction tower,
with its quotient augmentation. -/
def pbcActualCompletedPull : PbcCompletedDerived Y d ⥤ PbcCompletedDerived X d :=
  pbcActualDerivedPull g d ⋙ pbcActualCompletion d X

/-- The comparison is the actual completion unit after ordinary derived pullback. -/
def pbcActualCompletedPullUnit : pbcActualDerivedPull g d ⟶ pbcActualCompletedPull g d :=
  whiskerLeft (pbcActualDerivedPull g d) (pbcActualCompletionUnit d X)

/-- The completion reflection lands in the actual intrinsic complete predicate. -/
theorem pbcActualCompletedPull_isComplete (K : PbcCompletedDerived Y d) :
    PbcIsIntrinsicallyComplete X d ((pbcActualCompletedPull g d).obj K) := by
  exact ((ObjectProperty.ι (PbcIsIntrinsicallyComplete X d)).leftAdjoint.obj
    ((pbcActualDerivedPull g d).obj K)).property

private theorem actualReflection (S : Scheme.{u})
    (M N : PbcCompletedDerived S d) (hN : PbcIsIntrinsicallyComplete S d N) :
    Function.Bijective (fun f : (pbcActualCompletion d S).obj M ⟶ N ↦
      (pbcActualCompletionUnit d S).app M ≫ f) := by
  let P : ObjectProperty (PbcCompletedDerived S d) := PbcIsIntrinsicallyComplete S d
  let adj := Adjunction.ofIsRightAdjoint P.ι
  let e := (ObjectProperty.fullyFaithfulι P).homEquiv.symm.trans
    (adj.homEquiv M ⟨N, hN⟩)
  exact e.bijective

private theorem actualCompletion_unit_iso (S : Scheme.{u})
    (M : PbcCompletedDerived S d) (hM : PbcIsIntrinsicallyComplete S d M) :
    IsIso ((pbcActualCompletionUnit d S).app M) := by
  let P : ObjectProperty (PbcCompletedDerived S d) := PbcIsIntrinsicallyComplete S d
  exact (Adjunction.ofIsRightAdjoint P.ι).isIso_unit_app_iff_mem_essImage.mpr
    ⟨⟨M, hM⟩, ⟨Iso.refl _⟩⟩

private theorem actualCompletion_complete (S : Scheme.{u}) (M : PbcCompletedDerived S d) :
    PbcIsIntrinsicallyComplete S d ((pbcActualCompletion d S).obj M) :=
  ((ObjectProperty.ι (PbcIsIntrinsicallyComplete S d)).leftAdjoint.obj M).property

private theorem reflectionComparison
    {C : Type*} [Category C] (P : C → Prop)
    (F G : C ⥤ C) (η : 𝟭 C ⟶ F) (ε : 𝟭 C ⟶ G)
    (hF : ∀ M, P (F.obj M)) (hG : ∀ M, P (G.obj M))
    (rF : ∀ M N, P N → Function.Bijective (fun f : F.obj M ⟶ N ↦ η.app M ≫ f))
    (rG : ∀ M N, P N → Function.Bijective (fun f : G.obj M ⟶ N ↦ ε.app M ≫ f)) :
    ∃ e : F ≅ G, ∀ M, η.app M ≫ e.hom.app M = ε.app M := by
  classical
  choose f hf using fun M ↦ (rF M (G.obj M) (hG M)).surjective (ε.app M)
  choose g hg using fun M ↦ (rG M (F.obj M) (hF M)).surjective (η.app M)
  change ∀ M, η.app M ≫ f M = ε.app M at hf
  change ∀ M, ε.app M ≫ g M = η.app M at hg
  have hfg (M : C) : f M ≫ g M = 𝟙 _ := by
    apply (rF M (F.obj M) (hF M)).injective
    change η.app M ≫ (f M ≫ g M) = η.app M ≫ 𝟙 _
    rw [← Category.assoc, hf, hg, Category.comp_id]
  have hgf (M : C) : g M ≫ f M = 𝟙 _ := by
    apply (rG M (G.obj M) (hG M)).injective
    change ε.app M ≫ (g M ≫ f M) = ε.app M ≫ 𝟙 _
    rw [← Category.assoc, hg, hf, Category.comp_id]
  refine ⟨NatIso.ofComponents (fun M ↦ ⟨f M, g M, hfg M, hgf M⟩) ?_, hf⟩
  intro M N a
  apply (rF M (G.obj N) (hG N)).injective
  change η.app M ≫ (F.map a ≫ f N) = η.app M ≫ (f M ≫ G.map a)
  rw [← Category.assoc, ← η.naturality a, Category.assoc, hf, ← Category.assoc, hf]
  exact ε.naturality a

private theorem actualCompletion_quotient (S : Scheme.{u}) :
    ∃ e : pbcActualCompletion d S ≅
        completedReductionTower S d ⋙ completedRlim S (d.completedRing S),
      ∀ M, (pbcActualCompletionUnit d S).app M ≫ e.hom.app M = d.completionUnit S M := by
  classical
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let G := completedReductionTower S d ⋙ completedRlim S (d.completedRing S)
  let ε : 𝟭 (d.derived S) ⟶ G :=
    (d.constantRlimAdjunction S).unit ≫
      whiskerRight (completedReductionTowerUnit d S) (completedRlim S (d.completedRing S))
  have he (M : PbcCompletedDerived S d) :
      ∃ e : wfCompletionObj S d r a ha M ≅ G.obj M,
        wfCompletionUnit S d r a ha M ≫ e.hom = ε.app M := by
    obtain ⟨e, he⟩ := completedKoszulQuotientComparison S d r a ha M
      (wfCompletionRepresentative S d M) (DerivedCategory.Q.objObjPreimageIso M)
    exact ⟨e, he⟩
  choose e he using he
  have hc (M) : PbcIsIntrinsicallyComplete S d (G.obj M) :=
    (actualComplete_iso S d (e M)).mp ((wfComplete_iff_presentation S d r a ha _).mp
      ((wfCompletionReflector S d r a ha).1 M))
  have hb (M N) (hN : PbcIsIntrinsicallyComplete S d N) :
      Function.Bijective (fun f : G.obj M ⟶ N ↦ ε.app M ≫ f) := by
    have h := ((wfCompletionReflector S d r a ha).2 M N
      ((wfComplete_iff_presentation S d r a ha N).mpr hN)).comp
      (Iso.homCongr (e M).symm (Iso.refl N)).bijective
    convert h using 1
    ext f
    change ε.app M ≫ f = wfCompletionUnit S d r a ha M ≫
      ((e M).hom ≫ f ≫ 𝟙 N)
    rw [Category.comp_id, ← Category.assoc, he]
  obtain ⟨c, hc⟩ := reflectionComparison (PbcIsIntrinsicallyComplete S d) _ G
    (pbcActualCompletionUnit d S) ε (actualCompletion_complete d S) hc
    (actualReflection d S) hb
  refine ⟨c, fun M ↦ (hc M).trans ?_⟩
  rfl

set_option linter.unusedVariables false in
/-- Completion has the unique shift comparison commuting with its actual unit. -/
theorem pbcActualCompletionShift_exists :
    ∃! q : (pbcActualCompletion d T).CommShift ℤ,
      (fun [qInst : (pbcActualCompletion d T).CommShift ℤ] ↦
        NatTrans.CommShift (pbcActualCompletionUnit d T) ℤ) (qInst := q) := by
  let P : ObjectProperty (PbcCompletedDerived T d) := PbcIsIntrinsicallyComplete T d
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ (actualComplete_iso T d e).mp h⟩
  have : P.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨fun M hM ↦ actualComplete_shift T d M hM n⟩⟩
  let L := P.ι.leftAdjoint
  let adj := Adjunction.ofIsRightAdjoint P.ι
  let sL : L.CommShift ℤ := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  dsimp only [pbcActualCompletion, pbcActualCompletionUnit]
  let q : (L ⋙ P.ι).CommShift ℤ := inferInstance
  have hq : (fun [_qInst : (L ⋙ P.ι).CommShift ℤ] ↦
      NatTrans.CommShift adj.unit ℤ) (_qInst := q) := inferInstance
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  let F := pbcActualCompletion d T
  let η := pbcActualCompletionUnit d T
  have square (s : F.CommShift ℤ) (hs : letI := s; NatTrans.CommShift η ℤ)
      (n : ℤ) (M : PbcCompletedDerived T d) :
      η.app (M⟦n⟧) ≫ (Functor.commShiftIso F (self := s) n).hom.app M =
        (shiftFunctor _ n).map (η.app M) := by
    let := s
    have := hs
    have h := (NatTrans.shift_app_comm η n M).symm
    change η.app (M⟦n⟧) ≫ _ = 𝟙 _ ≫ _ at h
    simpa only [Category.id_comp] using h
  apply commShift_ext
  intro n
  apply Iso.ext
  ext M
  let N : P.FullSubcategory :=
    ⟨(F.obj M)⟦n⟧, actualComplete_shift T d _ (L.obj M).property n⟩
  have he :
      (ObjectProperty.homMk ((Functor.commShiftIso F (self := q') n).hom.app M) :
        L.obj (M⟦n⟧) ⟶ N) =
      ObjectProperty.homMk ((Functor.commShiftIso F (self := q) n).hom.app M) := by
    apply (adj.homEquiv (M⟦n⟧) N).injective
    exact (square q' hq' n M).trans (square q hq n M).symm
  exact congrArg (fun f ↦ f.hom) he

/-- The unit-normalized shift of the completion reflector. -/
instance pbcActualCompletionShift : (pbcActualCompletion d T).CommShift ℤ :=
  (pbcActualCompletionShift_exists d T).exists.choose

/-- Completed pullback inherits ordinary pullback and completion shifts. -/
instance pbcActualCompletedPullShift : (pbcActualCompletedPull g d).CommShift ℤ :=
  inferInstanceAs ((pbcActualDerivedPull g d ⋙ pbcActualCompletion d X).CommShift ℤ)

private theorem actualPush_eq_datum : pbcActualDerivedPush g d = d.push g := by
  have hc : completedCoefficientMap g d = (d.integralRingIso g).hom := by
    apply limit.hom_ext
    intro n
    change completedCoefficientMap g d ≫ d.projection X n.unop =
      (d.integralRingIso g).hom ≫ d.projection X n.unop
    calc
      _ = completedCoefficientComponent g d n.unop := limit.lift_π _ n
      _ = _ := by
        rw [d.projection_comm]
        rfl
  have hm : completedModuleDirectImage g d =
      proEtaleRingModuleDirectImage g (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso g) := by
    unfold completedModuleDirectImage proEtaleRingModuleDirectImage
    unfold completedCoefficientDirectImageMap proEtaleRingDirectImageMap
    rw [hc]
    rfl
  change (completedModuleDirectImage g d).rightDerivedFunctor = _
  cases hm
  rfl

-- Use the perfect-projection tower mate and its completion-unit equation.
private theorem quotientDirectComparison :
    ∃ e : d.push g ⋙ (completedReductionTower Y d ⋙ completedRlim Y (d.completedRing Y)) ≅
        (completedReductionTower X d ⋙ completedRlim X (d.completedRing X)) ⋙ d.push g,
      ∀ M, d.completionUnit Y ((d.push g).obj M) ≫ e.hom.app M =
        (d.push g).map (d.completionUnit X M) := by
  let τ : d.push g ⋙ completedReductionTower Y d ⟶
      completedReductionTower X d ⋙ d.towerPush g :=
    { app := d.towerProjection g
      naturality := fun {_ _} f ↦ (d.towerProjection_properties g _).2.1 _ f }
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  let e := (associator (d.push g) (completedReductionTower Y d)
      (completedRlim Y (d.completedRing Y))).symm ≪≫
    Functor.isoWhiskerRight (asIso τ) (completedRlim Y (d.completedRing Y)) ≪≫
    associator (completedReductionTower X d) (d.towerPush g)
      (completedRlim Y (d.completedRing Y)) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower X d) (d.directImageRlimIso g).symm ≪≫
    (associator (completedReductionTower X d) (completedRlim X (d.completedRing X))
      (d.push g)).symm
  refine ⟨e, ?_⟩
  intro M
  change d.completionUnit Y ((d.push g).obj M) ≫
    (𝟙 _ ≫ (completedRlim Y (d.completedRing Y)).map (d.towerProjection g M) ≫
      𝟙 _ ≫ (d.directImageRlimIso g).inv.app ((completedReductionTower X d).obj M) ≫
      𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id, ← Category.assoc]
  rw [(d.towerProjection_properties g M).2.2]
  simp

/-- Direct image commutes with completion with the specified completion unit. -/
theorem pbcActualDirectCompletionIso_exists :
    ∃! e : pbcActualDerivedPush g d ⋙ pbcActualCompletion d Y ≅
        pbcActualCompletion d X ⋙ pbcActualDerivedPush g d,
      ∀ K : PbcCompletedDerived X d,
        (pbcActualCompletionUnit d Y).app ((pbcActualDerivedPush g d).obj K) ≫
            e.hom.app K =
          (pbcActualDerivedPush g d).map ((pbcActualCompletionUnit d X).app K) := by
  classical
  rw [actualPush_eq_datum g d]
  let G := d.push g
  let FX := pbcActualCompletion d X
  let FY := pbcActualCompletion d Y
  let ηX := pbcActualCompletionUnit d X
  let ηY := pbcActualCompletionUnit d Y
  obtain ⟨cX, hcX⟩ := actualCompletion_quotient d X
  obtain ⟨cY, hcY⟩ := actualCompletion_quotient d Y
  obtain ⟨δ, hδ⟩ := quotientDirectComparison g d
  let e : G ⋙ FY ≅ FX ⋙ G :=
    Functor.isoWhiskerLeft G cY ≪≫ δ ≪≫ Functor.isoWhiskerRight cX.symm G
  have he (M : PbcCompletedDerived X d) :
      ηY.app (G.obj M) ≫ e.hom.app M = G.map (ηX.app M) := by
    change ηY.app (G.obj M) ≫
      (cY.hom.app (G.obj M) ≫ δ.hom.app M ≫ G.map (cX.inv.app M)) = _
    rw [← Category.assoc, hcY, ← Category.assoc, hδ, ← G.map_comp, ← hcX]
    rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hG (M : PbcCompletedDerived X d) (hM : PbcIsIntrinsicallyComplete X d M) :
      PbcIsIntrinsicallyComplete Y d (G.obj M) := by
    have : IsIso (ηX.app M) := actualCompletion_unit_iso d X M hM
    have : IsIso (ηY.app (G.obj M) ≫ e.hom.app M) := by
      rw [he]
      infer_instance
    have : IsIso (ηY.app (G.obj M)) := IsIso.of_isIso_comp_right _ (e.hom.app M)
    exact (actualComplete_iso Y d (asIso (ηY.app (G.obj M)))).mpr
      (actualCompletion_complete d Y _)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M
  apply (actualReflection d Y (G.obj M) (G.obj (FX.obj M))
    (hG (FX.obj M) (actualCompletion_complete d X M))).injective
  exact (he' M).trans (he M).symm

/-- The completion comparison uniquely fixed by the quotient augmentation. -/
def pbcActualDirectCompletionIso := (pbcActualDirectCompletionIso_exists g d).exists.choose

end AlgebraicGeometry.Scheme
