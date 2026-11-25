/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.TorsionCompletionDefinitions
public import WeilConjectures.CategoryTheory.MultiplicationDifference
public import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.LocalHomTowerCriterion
import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.Algebra.Homology.LocalCoefficientTelescopeDual
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.CategoryTheory.SequentialTelescopeMono
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Module.ULift
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.ModuleLocalizationTowerVanishing
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-! # The multiplication difference on a pro-etale slice

## References

* Stacks Project, Tag 0997, Tag 099Q
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem module_equivalence
    {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J RingCat.{w}) (S : Sheaf K RingCat.{w})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{w} K J).obj R) :
    Nonempty (SheafOfModules.{w} R ≌ SheafOfModules.{w} S) := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{w} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact ⟨SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂⟩

private theorem conjugate_isIso_iff
    {B : Type*} [Category* B] {M N : B} (e : M ≅ N)
    (a : M ⟶ M) (b : N ⟶ N) (h : a ≫ e.hom = e.hom ≫ b) :
    IsIso a ↔ IsIso b := by
  have hb : b = e.inv ≫ a ≫ e.hom := by rw [h]; simp
  have ha : a = e.hom ≫ b ≫ e.inv := by rw [← Category.assoc, ← h]; simp
  constructor
  · intro hi
    have := hi
    rw [hb]
    infer_instance
  · intro hi
    have := hi
    rw [ha]
    infer_instance

private theorem tower_map_iso_iff
    {B D : Type*} [Category* B] [Preadditive B] [Category* D] [Preadditive D]
    (P : B ⥤ D) [P.Additive]
    (K : ℕ → B) [HasProduct K] [HasProduct (fun n ↦ P.obj (K n))]
    [PreservesLimit (Discrete.functor K) P] (a : ∀ n, K (n + 1) ⟶ K n) :
    IsIso (P.map (towerTransitionEndomorphism a)) ↔
      IsIso (towerTransitionEndomorphism (K := fun n ↦ P.obj (K n))
        (fun n ↦ P.map (a n))) := by
  let e := PreservesProduct.iso P K
  apply conjugate_isIso_iff e
  apply Pi.hom_ext
  intro n
  dsimp only [e]
  simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]
  rw [← P.map_comp, (towerTransitionEndomorphism_eq_iff a _).mp rfl n,
    P.map_sub, P.map_comp]
  simp [towerTransitionEndomorphism, towerProductShift]

private theorem complex_tower_isIso_of_components
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    (K : CochainComplex B ℤ) (a : K ⟶ K)
    (ha : ∀ i : ℤ, IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ K.X i) (fun _ ↦ a.f i))) :
    IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ ↦ a)) := by
  have (i : ℤ) : IsIso
      ((towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ ↦ a)).f i) :=
    (tower_map_iso_iff (HomologicalComplex.eval B (.up ℤ) i)
      (fun _ : ℕ ↦ K) (fun _ ↦ a)).mpr (ha i)
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem derived_tower_isIso_of_components
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    [HasCountableProducts B] [CountableAB4Star B]
    (K : CochainComplex B ℤ) (a : K ⟶ K)
    (ha : ∀ i : ℤ, IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ K.X i) (fun _ ↦ a.f i))) :
    let := (derivedCategory_countableProducts_core.{0} B).choose
    IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ DerivedCategory.Q.obj K) (fun _ ↦ DerivedCategory.Q.map a)) := by
  let := (derivedCategory_countableProducts_core.{0} B).choose
  have hP := (derivedCategory_countableProducts_core.{0} B).choose_spec.1 ℕ (fun _ ↦ K)
  let : PreservesLimit (Discrete.functor (fun _ : ℕ ↦ K)) DerivedCategory.Q :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) hP.some
  have := complex_tower_isIso_of_components K a ha
  apply (tower_map_iso_iff DerivedCategory.Q (fun _ : ℕ ↦ K) (fun _ ↦ a)).mp
  infer_instance

private theorem towerIso_of_iso
    {B : Type*} [Category* B] [Preadditive B] [HasCountableProducts B]
    {M N : B} (e : M ≅ N) (a : M ⟶ M) (b : N ⟶ N)
    (h : a ≫ e.hom = e.hom ≫ b) :
    IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ M) (fun _ ↦ a)) ↔
      IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ N) (fun _ ↦ b)) := by
  apply conjugate_isIso_iff (Pi.mapIso (fun _ : ℕ ↦ e))
  exact (towerTransitionEndomorphism_natural_backward _ _ (fun _ ↦ e.hom)
    (fun _ ↦ h.symm)).symm

private theorem localHom_iff_towerIso
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{v}) (U : C) (f : O.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{v} (localCoefficientRings O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{v} ((localCoefficientRings O).over U))]
    (K : DerivedCategory (ringedSiteModules.{v} (localCoefficientRings O)))
    [HasProduct (fun _ : ℕ ↦ (localCoefficientDerivedRestriction O U).obj K)] :
    IsZero ((derivedInternalHom (J.over U) (O.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (localCoefficientLocalization O U f)),
        (localCoefficientDerivedRestriction O U).obj K)) ↔
      IsIso (towerTransitionEndomorphism
        (K := fun _ : ℕ ↦ (localCoefficientDerivedRestriction O U).obj K)
        (fun _ ↦ (localSectionDerivedMultiplication O U f).app K)) := by
  obtain ⟨T, hT⟩ := (exists_isDerivedLimit_and_iso
    (fun _ : ℕ ↦ (localCoefficientDerivedRestriction O U).obj K)
    (fun _ ↦ (localSectionDerivedMultiplication O U f).app K)).1
  have h := localHom_zero_iff_multiplicationTower_zero J O U f K T hT
  obtain ⟨p, δ, hδ⟩ := hT
  exact h.trans (Pretriangulated.Triangle.isZero₁_iff_isIso₂
    (Pretriangulated.Triangle.mk p _ δ) hδ)

private theorem multiplication_fac
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{v}) (U : C) (f : O.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{v} (localCoefficientRings O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{v} ((localCoefficientRings O).over U))]
    (K : CochainComplex (ringedSiteModules.{v} (localCoefficientRings O)) ℤ) :
    let := (localCoefficientRestriction_exact O U).1
    let := (localCoefficientRestriction_exact O U).2.1
    let := (localCoefficientRestriction_exact O U).2.2
    let T : ringedSiteModules.{v} (localCoefficientRings O) ⥤
        ringedSiteModules.{v} ((localCoefficientRings O).over U) :=
      SheafOfModules.overFunctor.{v} (localCoefficientRings O) U
    (localSectionDerivedMultiplication O U f).app (DerivedCategory.Q.obj K) ≫
        T.mapDerivedCategoryFactors.hom.app K =
      T.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (localSectionMultiplicationNatTrans O U f)
          (.up ℤ)).app K) := by
  have := (localCoefficientRestriction_exact O U).1
  have := (localCoefficientRestriction_exact O U).2.1
  have := (localCoefficientRestriction_exact O U).2.2
  dsimp only
  simp only [localSectionDerivedMultiplication, Localization.liftNatTrans_app,
    Category.assoc]
  let T : ringedSiteModules.{v} (localCoefficientRings O) ⥤
      ringedSiteModules.{v} ((localCoefficientRings O).over U) :=
    SheafOfModules.overFunctor.{v} (localCoefficientRings O) U
  change _ ≫ (_ ≫
    (T.mapDerivedCategoryFactors.inv.app K ≫ T.mapDerivedCategoryFactors.hom.app K)) = _
  rw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem localHom_zero_of_termwise_difference
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{v}) (U : C) (f : O.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{v} (localCoefficientRings O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{v} ((localCoefficientRings O).over U))]
    [CountableAB4Star (ringedSiteModules.{v} ((localCoefficientRings O).over U))]
    (K : CochainComplex (ringedSiteModules.{v} (localCoefficientRings O)) ℤ)
    (hK : ∀ i : ℤ, IsIso ((multiplicationDifference O U f).app ((K.X i).over U))) :
    IsZero ((derivedInternalHom (J.over U) (O.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (localCoefficientLocalization O U f)),
        (localCoefficientDerivedRestriction O U).obj (DerivedCategory.Q.obj K))) := by
  let B := ringedSiteModules.{v} ((localCoefficientRings O).over U)
  let := (derivedCategory_countableProducts_core.{0} B).choose
  have := (localCoefficientRestriction_exact O U).1
  have := (localCoefficientRestriction_exact O U).2.1
  have := (localCoefficientRestriction_exact O U).2.2
  apply (localHom_iff_towerIso J O U f _).mpr
  let T : ringedSiteModules.{v} (localCoefficientRings O) ⥤
      ringedSiteModules.{v} ((localCoefficientRings O).over U) :=
    SheafOfModules.overFunctor.{v} (localCoefficientRings O) U
  let L := (T.mapHomologicalComplex (.up ℤ)).obj K
  let a := (NatTrans.mapHomologicalComplex
    (localSectionMultiplicationNatTrans O U f) (.up ℤ)).app K
  apply (towerIso_of_iso (T.mapDerivedCategoryFactors.app K) _
    (DerivedCategory.Q.map a) (multiplication_fac O U f K)).mpr
  exact derived_tower_isIso_of_components L a hK

private theorem coefficientLocalizationIso
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{v}) (U : C) (f : O.obj.obj (op U)) :
    Nonempty (localCoefficientLocalization O U f ≅
      ringedSectionLocalization (O.over U) (ringedSliceSection O U f)) := by
  have hm : localSectionMultiplication O U f (SheafOfModules.unit _) =
      (SheafOfModules.unitHomEquiv _).symm
        ⟨(ringedSliceSection O U f).val, (ringedSliceSection O U f).property⟩ := by
    apply (SheafOfModules.forget _).map_injective
    apply PresheafOfModules.Hom.ext
    funext V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change O.obj.obj (op V.unop.left) at x
    change O.obj.map V.unop.hom.op f * x = x * O.obj.map V.unop.hom.op f
    exact mul_comm _ _
  obtain ⟨c, ⟨hc⟩, e, _⟩ :=
    scalarLocalization_regularColimit (O.over U) (ringedSliceSection O U f)
  unfold localCoefficientLocalization
  simp_rw [hm]
  exact ⟨colimit.isoColimitCocone ⟨c, hc⟩ ≪≫ e⟩

end AlgebraicGeometry.Scheme
