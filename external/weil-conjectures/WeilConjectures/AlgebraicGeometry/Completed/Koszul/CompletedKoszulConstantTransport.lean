/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulRoosComparison
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulLimitComparison
import WeilConjectures.CategoryTheory.Ringed.RingedPresentationTransport
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
import WeilConjectures.Algebra.Homology.InternalHom
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation
import WeilConjectures.CategoryTheory.RingedKoszulDualizable
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic
import WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower
import WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
import WeilConjectures.Algebra.Homology.TelescopeColimit
import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
import WeilConjectures.CategoryTheory.RingedAugmentedCechRestriction
import WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
import WeilConjectures.CategoryTheory.LocalizationRHom.RingedLocalizationRestrictionSupplement
import WeilConjectures.Algebra.Homology.SliceTensorNatural
import WeilConjectures.Algebra.Homology.SliceModuleSheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Transport of the two strict completion presentations to the small constant site

Source: Stacks Tags 03CR, 05RR, 06YY and 0941.
(blueprint: lem-weil-pbc-completed-koszul-constant-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

private theorem ideal_generated_global_sections
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{t}) (I : RingedSiteIdeal R)
    (r : ℕ) (b : Fin r → (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (hs : ∀ U : C, I.sections U =
      Ideal.span (Set.range (fun i ↦ (b i).val (op U)))) :
    ∃ σ : I.module.GeneratingSections, ∃ e : σ.I ≃ Fin r,
      ∀ i : σ.I, SheafOfModules.sectionsMap I.inclusion (σ.s i) = b (e i) := by
  classical
  let s (i : ULift.{t} (Fin r)) : I.module.sections :=
    { val := fun U ↦ ⟨(b i.down).val U, by
        rw [hs]
        exact Ideal.subset_span ⟨i.down, rfl⟩⟩
      property := by
        intro U V f
        apply Subtype.ext
        exact (b i.down).property f }
  let π := I.module.freeHomEquiv.symm s
  have hπ : Epi π := by
    constructor
    intro M f g hfg
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let x' : I.sections U.unop := x
    have hx : (x' : R.obj.obj U) ∈
        Ideal.span (Set.range (fun i ↦ (b i).val U)) := by
      rw [← hs]
      exact x'.property
    have hgen (i : ULift.{t} (Fin r)) :
        f.val.app U (s i |>.val U) = g.val.app U (s i |>.val U) := by
      have h := congrArg (fun k ↦
        (SheafOfModules.sectionsMap k (SheafOfModules.freeSection i)).val U) hfg
      dsimp only [π] at h
      have h' := h
      simp only [SheafOfModules.sectionsMap_comp,
        SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection] at h
      exact h
    have hind : ∀ (y : R.obj.obj U),
        y ∈ Ideal.span (Set.range (fun i ↦ (b i).val U)) →
        ∀ hy : y ∈ I.sections U.unop,
          f.val.app U ⟨y, hy⟩ = g.val.app U ⟨y, hy⟩ := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨i, rfl⟩
          intro hi
          exact hgen ⟨i⟩
      | zero =>
          intro hzero
          change f.val.app U 0 = g.val.app U 0
          simp only [map_zero]
      | add y z hy hz ihy ihz =>
          intro hsum
          change f.val.app U (⟨y, by rw [hs]; exact hy⟩ +
              ⟨z, by rw [hs]; exact hz⟩) = _
          rw [map_add, ihy, ihz]
          exact (map_add (g.val.app U).hom _ _).symm
      | smul c y hy ih =>
          intro hprod
          change f.val.app U (c • ⟨y, by rw [hs]; exact hy⟩) = _
          rw [map_smul, ih]
          exact (map_smul (g.val.app U).hom c _).symm
    exact hind x'.val hx x'.property
  refine ⟨{ I := ULift.{t} (Fin r), s := s, epi := hπ }, Equiv.ulift, ?_⟩
  intro i
  rfl

private theorem global_generators_on_slice
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{t}) (I : RingedSiteIdeal R)
    (r : ℕ) (b : Fin r → (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (σ : I.module.GeneratingSections) (e : σ.I ≃ Fin r)
    (he : ∀ i : σ.I, SheafOfModules.sectionsMap I.inclusion (σ.s i) = b (e i))
    (U : C) : IsRingedIdealGeneratingList R I.module I.inclusion U r
      (fun i ↦ (b i).val (op U)) := by
  classical
  let F := SheafOfModules.overFunctor (siteModuleRings R) U
  have hcolim : PreservesColimitsOfSize.{t, t} F := by
    let H := (Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{t} (J.over U) J
    have : PreservesColimitsOfSize.{t, t} H :=
      ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{t}
        (J.over U) J).leftAdjoint_preservesColimits
    have : PreservesColimitsOfSize.{t, t} (SheafOfModules.toSheaf.{t} (siteModuleRings R)) :=
      ⟨fun {L} _ ↦ ((moduleSheaves_colimits_forgetful.{t, t, t, t}
        (siteModuleRings R)).2.2.2.2.2 L).2.1⟩
    have : PreservesColimitsOfSize.{t, t}
        (F ⋙ SheafOfModules.toSheaf.{t} ((siteModuleRings R).over U)) :=
      inferInstanceAs (PreservesColimitsOfSize.{t, t}
        (SheafOfModules.toSheaf.{t} (siteModuleRings R) ⋙ H))
    have : ReflectsColimitsOfSize.{t, t}
        (SheafOfModules.toSheaf.{t} ((siteModuleRings R).over U)) :=
      ⟨fun {_} _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
    exact preservesColimits_of_reflects_of_preserves F
      (SheafOfModules.toSheaf.{t} ((siteModuleRings R).over U))
  let τ := σ.map F (Iso.refl _)
  refine ⟨τ, e, ?_⟩
  intro i
  let s : (I.module.over U).sections :=
    { val := fun V ↦ (σ.s i).val (op V.unop.left)
      property := fun f ↦ (σ.s i).property ((Over.forget U).op.map f) }
  have hs : τ.s i = s := by
    apply (I.module.over U).unitHomEquiv.symm.injective
    dsimp only [τ, SheafOfModules.GeneratingSections.map,
      SheafOfModules.GeneratingSections.mapFreeHom]
    rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
      SheafOfModules.ιFree_mapFreeIso_hom_assoc]
    dsimp only [Iso.refl_hom]
    rw [Category.id_comp, ← F.map_comp,
      ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    dsimp only [SheafOfModules.GeneratingSections.π]
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hs]
  have h := congrArg (fun q ↦ q.val (op U)) (he i)
  exact h

private def coefficientSectionHom
    {C : Type t} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type t) [CommRing A] {O : Sheaf J CommRingCat.{t}}
    (φ : ConstantCompletion.constant J A ⟶ O) (U : Cᵒᵖ) : A →+* O.obj.obj U :=
  (φ.hom.app U).hom.comp
    ((toSheafify J ((CategoryTheory.Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U).hom

private theorem span_subtype_images
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) {ι : Type*} (a : ι → A) (ha : Ideal.span (Set.range a) = I) :
    Ideal.span (Set.range (fun x : I ↦ f x)) =
      Ideal.span (Set.range (fun i ↦ f (a i))) := by
  have h : Ideal.span (Set.range (fun x : I ↦ f x)) = Ideal.map f I := by
    unfold Ideal.map
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [h, ← ha, Ideal.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨a i, ⟨i, rfl⟩, rfl⟩

private theorem constant_kernel_generated
    {C : Type t} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type t) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (U : C) :
    (ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0)).sections U =
      Ideal.span (Set.range (fun i ↦
        (ConstantCompletion.algebraSection (ConstantCompletion.coefficientMap J A I)
          (a i)).val (op U))) := by
  have hk : (ConstantCompletion.kernelIdeal
      (ConstantCompletion.projection J A I 0)).sections U =
      RingHom.ker ((ConstantCompletion.projection J A I 0).hom.app (op U)).hom :=
    (ConstantCompletion.kernelIdeal_existsUnique
      (ConstantCompletion.projection J A I 0)).exists.choose_spec U
  rw [hk]
  have h := ((ConstantCompletion.flat_and_quotients J A I).2.1 0 U).2
  rw [h]
  exact span_subtype_images
    (coefficientSectionHom J A (ConstantCompletion.coefficientMap J A I) (op U))
    (I ^ (0 + 1)) a (by simpa only [Nat.zero_add, pow_one] using ha)

private def sectionRingEquiv
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{t}} (e : R ≅ S) (U : Cᵒᵖ) :
    R.obj.obj U ≃+* S.obj.obj U where
  toFun := e.hom.hom.app U
  invFun := e.inv.hom.app U
  left_inv x := ConcreteCategory.congr_hom
    (congrArg (fun q : R ⟶ R ↦ q.hom.app U) e.hom_inv_id) x
  right_inv x := ConcreteCategory.congr_hom
    (congrArg (fun q : S ⟶ S ↦ q.hom.app U) e.inv_hom_id) x
  map_mul' := map_mul (e.hom.hom.app U).hom
  map_add' := map_add (e.hom.hom.app U).hom

private def comapIdealIso
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{t}} (e : R ≅ S) (I : RingedSiteIdeal S) :
    RingedSiteIdeal R where
  sections U := Ideal.comap (e.hom.hom.app (op U)).hom (I.sections U)
  restriction := by
    intro U V g a ha
    change e.hom.hom.app (op V) (R.obj.map g.op a) ∈ I.sections V
    have h := ConcreteCategory.congr_hom (e.hom.hom.naturality g.op) a
    change e.hom.hom.app (op V) (R.obj.map g.op a) =
      S.obj.map g.op (e.hom.hom.app (op U) a) at h
    rw [h]
    exact I.restriction g _ ha
  local_mem := by
    intro U a L hL ha
    apply I.local_mem U (e.hom.hom.app (op U) a) L hL
    intro V g hg
    have h := ConcreteCategory.congr_hom (e.hom.hom.naturality g.op) a
    change e.hom.hom.app (op V) (R.obj.map g.op a) =
      S.obj.map g.op (e.hom.hom.app (op U) a) at h
    rw [← h]
    exact ha V g hg

private theorem extension_iso_eq
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{t}} (e : R ≅ S) (I : RingedSiteIdeal S) :
    I.extension e.inv = comapIdealIso e I := by
  let K := comapIdealIso e I
  have hK : ∀ (U : C) (x : R.obj.obj (op U)), x ∈ K.sections U ↔
      ∃ L : Sieve U, L ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), L g →
        R.obj.map g.op x ∈ Ideal.span (Set.range
          (fun a : I.sections V ↦ e.inv.hom.app (op V) a)) := by
    intro U x
    constructor
    · intro hx
      refine ⟨⊤, J.top_mem U, ?_⟩
      intro V g hg
      have hy := K.restriction g x hx
      let y := R.obj.map g.op x
      have heq : e.inv.hom.app (op V) (e.hom.hom.app (op V) y) = y :=
        (sectionRingEquiv e (op V)).left_inv y
      change y ∈ _
      rw [← heq]
      exact Ideal.subset_span ⟨⟨e.hom.hom.app (op V) y, hy⟩, rfl⟩
    · rintro ⟨L, hL, hx⟩
      apply K.local_mem U x L hL
      intro V g hg
      have hs : Ideal.span (Set.range
          (fun a : I.sections V ↦ e.inv.hom.app (op V) a)) ≤ K.sections V := by
        apply Ideal.span_le.mpr
        rintro _ ⟨a, rfl⟩
        change e.hom.hom.app (op V) (e.inv.hom.app (op V) a.val) ∈ I.sections V
        have heq : e.hom.hom.app (op V) (e.inv.hom.app (op V) a.val) = a.val :=
          (sectionRingEquiv e (op V)).right_inv a.val
        rw [heq]
        exact a.property
      exact hs (hx V g hg)
  exact ((I.existsUnique_extension e.inv).unique
    (I.existsUnique_extension e.inv).exists.choose_spec hK)

private theorem comapIdealIso_sections_span
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{t}} (e : R ≅ S) (I : RingedSiteIdeal S)
    {ι : Type*} (b : ι → (S.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (hs : ∀ U : C, I.sections U = Ideal.span (Set.range (fun i ↦ (b i).val (op U))))
    (U : C) :
    (comapIdealIso e I).sections U = Ideal.span (Set.range
      (fun i ↦ e.inv.hom.app (op U) ((b i).val (op U)))) := by
  change Ideal.comap (sectionRingEquiv e (op U)).toRingHom (I.sections U) = _
  erw [← Ideal.map_symm (sectionRingEquiv e (op U)), hs, Ideal.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(b i).val (op U), ⟨i, rfl⟩, rfl⟩

private theorem reflectors_unit_iso
    {B : Type*} [Category* B] (P : B → Prop)
    {X Y Z : B} (η : X ⟶ Y) (μ : X ⟶ Z) (hY : P Y) (hZ : P Z)
    (hη : ∀ L, P L → Function.Bijective (fun f : Y ⟶ L ↦ η ≫ f))
    (hμ : ∀ L, P L → Function.Bijective (fun f : Z ⟶ L ↦ μ ≫ f)) :
    ∃ e : Y ≅ Z, η ≫ e.hom = μ := by
  obtain ⟨f, hf⟩ := (hη Z hZ).surjective μ
  obtain ⟨g, hg⟩ := (hμ Y hY).surjective η
  dsimp only at hf hg
  refine ⟨{ hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }, hf⟩
  · apply (hη Y hY).injective
    dsimp only
    rw [← Category.assoc, hf, hg, Category.comp_id]
  · apply (hμ Z hZ).injective
    dsimp only
    rw [← Category.assoc, hg, hf, Category.comp_id]

private theorem reflector_transport_universal
    {B H : Type*} [Category* B] [Category* H] (E : B ≌ H)
    (P : B → Prop) (P' : H → Prop)
    (hP : ∀ L, P L ↔ P' (E.functor.obj L))
    (hiso : ∀ {L M : H}, (L ≅ M) → P' M → P' L)
    {X Y : B} (η : X ⟶ Y)
    (hη : ∀ L, P L → Function.Bijective (fun f : Y ⟶ L ↦ η ≫ f))
    (L : H) (hL : P' L) :
    Function.Bijective (fun f : E.functor.obj Y ⟶ L ↦ E.functor.map η ≫ f) := by
  let Z := E.inverse.obj L
  let e : E.functor.obj Z ≅ L := E.counitIso.app L
  have hZ : P Z := (hP Z).mpr (hiso e hL)
  constructor
  · intro f g hfg
    dsimp only at hfg
    have h : η ≫ E.functor.preimage (f ≫ e.inv) =
        η ≫ E.functor.preimage (g ≫ e.inv) := by
      apply E.functor.map_injective
      rw [E.functor.map_comp, E.functor.map_comp,
        E.functor.map_preimage, E.functor.map_preimage, ← Category.assoc, hfg, Category.assoc]
    have h' := congrArg E.functor.map ((hη Z hZ).injective h)
    rw [E.functor.map_preimage, E.functor.map_preimage] at h'
    exact (cancel_mono e.inv).mp h'
  · intro f
    obtain ⟨a, ha⟩ := (hη Z hZ).surjective (E.functor.preimage (f ≫ e.inv))
    dsimp only at ha
    refine ⟨E.functor.map a ≫ e.hom, ?_⟩
    dsimp only
    rw [← Category.assoc, ← E.functor.map_comp, ha,
      E.functor.map_preimage, Category.assoc, e.inv_hom_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringIsoRestrictionEquiv
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{t}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{t} c.hom).IsEquivalence := by
  let ec : C ≌ C := CategoryTheory.Equivalence.refl
  have : ec.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : ec.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let e := SheafOfModules.pushforwardPushforwardEquivalence (J := J) (K := J)
    ec c.hom c.inv
    (by
      ext U x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      simpa only [S.obj.map_id, ObjectProperty.FullSubcategory.id_hom,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.id_app, NatTrans.comp_app,
        RingCat.hom_id, RingCat.hom_comp, RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : S ⟶ S ↦ (f.hom.app U).hom x) c.inv_hom_id.symm)
    (by
      ext U x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      simpa only [R.obj.map_id, ObjectProperty.FullSubcategory.id_hom,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.id_app, NatTrans.comp_app,
        RingCat.hom_id, RingCat.hom_comp, RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : R ⟶ R ↦ (f.hom.app U).hom x) c.hom_inv_id)
  have h : SheafOfModules.restrictScalars.{t} c.hom = e.functor := by rfl
  rw [h]
  exact e.isEquivalence_functor

private def ringIsoDerivedEquiv
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{t}} (e : R ≅ S)
    [HasDerivedCategory.{t + 1} (SheafOfModules.{t} (siteModuleRings R))]
    [HasDerivedCategory.{t + 1} (SheafOfModules.{t} (siteModuleRings S))] :
    ringedSiteDerived R ≌ ringedSiteDerived S := by
  let F := SheafOfModules.restrictScalars.{t}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map e.inv)
  have : F.IsEquivalence :=
    ringIsoRestrictionEquiv ((sheafCompose J (forget₂ CommRingCat RingCat)).mapIso e.symm)
  have : F.asEquivalence.functor.Additive := inferInstanceAs F.Additive
  exact F.asEquivalence.mapDerivedCategory

private theorem ideal_inclusion_mono
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{t}} (I : RingedSiteIdeal R) : Mono I.inclusion := by
  constructor
  intro M f g h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.val.app U) h) x

private theorem ringIdealReflectorTransport
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{t}} (e : R ≅ S) (I : RingedSiteIdeal S)
    [HasDerivedCategory.{t + 1} (SheafOfModules.{t} (siteModuleRings R))]
    [HasDerivedCategory.{t + 1} (SheafOfModules.{t} (siteModuleRings S))]
    [HasDerivedCategory.{t + 1} (ℕᵒᵖ ⥤ SheafOfModules.{t} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{t + 1} (SheafOfModules.{t} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{t + 1} (SheafOfModules.{t} (siteModuleRings (S.over U)))]
    (r : ℕ) (b : Fin r → (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (hgen : ∀ U, IsRingedIdealGeneratingList R (comapIdealIso e I).module
      (comapIdealIso e I).inclusion U r (fun i ↦ (b i).val (op U)))
    (T : ringedSiteDerived S ⥤ ringedSiteDerived S) (μ : 𝟭 _ ⟶ T)
    (hT : ∀ N, IsLocallyDerivedRingedIdealComplete S I.module I.inclusion (T.obj N))
    (hμ : ∀ N L, IsLocallyDerivedRingedIdealComplete S I.module I.inclusion L →
      Function.Bijective (fun f : T.obj N ⟶ L ↦ μ.app N ≫ f)) :
    ∃ D : RingedKoszulLimitPresentation R r b,
      ∀ N : ringedSiteDerived R,
        ∃ k : (ringIsoDerivedEquiv e).functor.obj (D.completion.obj N) ≅
            T.obj ((ringIsoDerivedEquiv e).functor.obj N),
          (ringIsoDerivedEquiv e).functor.map (D.unit N) ≫ k.hom =
            μ.app ((ringIsoDerivedEquiv e).functor.obj N) := by
  let K := comapIdealIso e I
  have : Mono K.inclusion := ideal_inclusion_mono K
  obtain ⟨D, hD, hη, _⟩ := ringedKoszulCompletionReflector R r b K.module K.inclusion hgen
  let E := ringIsoDerivedEquiv e
  let P := IsLocallyDerivedRingedIdealComplete R K.module K.inclusion
  let P' := IsLocallyDerivedRingedIdealComplete S I.module I.inclusion
  have hP : ∀ N, P N ↔ P' (E.functor.obj N) := by
    intro N
    have h := siteDerivedRestrictScalars_locallyDerivedComplete_iff e.inv I N
    rw [extension_iso_eq e I] at h
    exact h.symm
  have hiso : ∀ {L M : ringedSiteDerived S}, (L ≅ M) → P' M → P' L := by
    intro L M k hM
    exact CategoryTheory.locallyDerivedRingedIdealComplete_of_iso S I k hM
  refine ⟨D, fun N ↦ ?_⟩
  exact reflectors_unit_iso P' (E.functor.map (D.unit N)) (μ.app (E.functor.obj N))
    ((hP _).mp (hD N)) (hT _)
    (reflector_transport_universal E P P' hP hiso (D.unit N) (hη N))
    (hμ (E.functor.obj N))

private instance smallSheafDerived
    {C : Type t} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{t}) : HasDerivedCategory (SheafOfModules.{t} (siteModuleRings R)) :=
  HasDerivedCategory.standard _

private theorem cech_kernel_generators
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (β : completedCechRing T d ≅
      ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true)
    (hβ : ∀ (U : (completedCechSite T)ᵒᵖ) (x : A),
      β.hom.hom.app U ((completedCechScalar T d x).val U) =
        (ConstantCompletion.algebraSection
          (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal) x).val U)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    let I := ConstantCompletion.kernelIdeal
      (ConstantCompletion.projection (completedCechTopology T) A d.ideal 0)
    let K := comapIdealIso β I
    ∀ U, IsRingedIdealGeneratingList (completedCechRing T d) K.module K.inclusion U r
      (fun i ↦ (completedCechScalar T d (a i)).val (op U)) := by
  let := d.noetherian
  let I := ConstantCompletion.kernelIdeal
    (ConstantCompletion.projection (completedCechTopology T) A d.ideal 0)
  let e := β
  let K := comapIdealIso e I
  have hs : ∀ U, K.sections U = Ideal.span (Set.range
      (fun i ↦ (completedCechScalar T d (a i)).val (op U))) := by
    intro U
    have h := comapIdealIso_sections_span e I
      (fun i ↦ ConstantCompletion.algebraSection
        (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal) (a i))
      (fun V ↦ constant_kernel_generated _ A d.ideal r a ha V) U
    change K.sections U = _ at h
    rw [h]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    apply (sectionRingEquiv e (op U)).injective
    change e.hom.hom.app (op U) (e.inv.hom.app (op U) _) =
      e.hom.hom.app (op U) ((completedCechScalar T d (a i)).val (op U))
    change (sectionRingEquiv e (op U))
      ((sectionRingEquiv e (op U)).symm _) = _
    rw [RingEquiv.apply_symm_apply]
    exact (hβ (op U) (a i)).symm
  obtain ⟨σ, q, hσ⟩ := ideal_generated_global_sections (completedCechRing T d) K r
    (fun i ↦ completedCechScalar T d (a i)) hs
  exact global_generators_on_slice (completedCechRing T d) K r
    (fun i ↦ completedCechScalar T d (a i)) σ q hσ

private def cechConstantDerivedEquiv
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (β : completedCechRing T d ≅
      ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true) :
    d.derived T ≌ ConstantCompletion.D
      (ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true) :=
  (completedCechDerivedEquiv T d).trans (ringIsoDerivedEquiv β)

private theorem koszul_to_constant_completion
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (β : completedCechRing T d ≅
      ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true)
    (hβ : ∀ (U : (completedCechSite T)ᵒᵖ) (x : A),
      β.hom.hom.app U ((completedCechScalar T d x).val U) =
        (ConstantCompletion.algebraSection
          (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal) x).val U)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ∃ e : (cechConstantDerivedEquiv T d β).functor.obj
        (DerivedCategory.Q.obj (intrinsicCompletionComplex T d r a C)) ≅
      (ConstantCompletion.completion (completedCechTopology T) A d.ideal true).obj
        ((cechConstantDerivedEquiv T d β).functor.obj (DerivedCategory.Q.obj C)),
      (cechConstantDerivedEquiv T d β).functor.map
        (DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a C)) ≫ e.hom =
          (ConstantCompletion.completionUnit (completedCechTopology T) A d.ideal true).app
            ((cechConstantDerivedEquiv T d β).functor.obj (DerivedCategory.Q.obj C)) := by
  let := d.noetherian
  let J := completedCechTopology T
  let B := ConstantCompletion.coefficients J A d.ideal true
  let I := ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A d.ideal 0)
  let : ∀ U : completedCechSite T, HasDerivedCategory.{t + 2}
      (SheafOfModules.{t + 1} (siteModuleRings ((completedCechRing T d).over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ U : completedCechSite T, HasDerivedCategory.{t + 2}
      (SheafOfModules.{t + 1} (siteModuleRings (B.over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  obtain ⟨_, _, hT, hμ, _⟩ :=
    ConstantCompletion.koszul_quotient_reflector J A d.ideal true r a ha
  obtain ⟨D, hD⟩ := ringIdealReflectorTransport β I r
    (fun i ↦ completedCechScalar T d (a i)) (cech_kernel_generators T d β hβ r a ha)
    (ConstantCompletion.completion J A d.ideal true)
    (ConstantCompletion.completionUnit J A d.ideal true) hT hμ
  obtain ⟨e, he⟩ := completed_fiber_strict_limit_comparison T d r a C D
  obtain ⟨k, hk⟩ := hD ((completedCechDerivedEquiv T d).functor.obj (DerivedCategory.Q.obj C))
  let E := ringIsoDerivedEquiv β
  refine ⟨E.functor.mapIso e ≪≫ k, ?_⟩
  change E.functor.map _ ≫ E.functor.map e.hom ≫ k.hom = _
  rw [← E.functor.map_comp_assoc, he, hk]
  rfl

set_option linter.style.haveILetI false in
/-- A scalar-preserving completed coefficient isomorphism carries the localized
Koszul fiber and its specified unit to constant-sheaf quotient completion.

Source: Stacks Tags 099L, 099M and 0A0E.
(blueprint: lem-weil-pbc-completed-koszul-constant-transport).

Proof: the kernel ideal of the first constant quotient is generated sectionwise by the
images of the chosen generators. Pulling this ideal along the ring isomorphism gives
the corresponding ideal on the small completed site. These global generators give
surjections from finite free module sheaves on every slice. The ringed Koszul reflector
therefore exists for this ideal. Exact restriction along the ring isomorphism preserves
local derived completeness, so uniqueness of reflections gives its unit-preserving
comparison with constant quotient completion. The completed fiber/strict-limit
comparison identifies the published Koszul fiber with this reflector, with its unit.
Finally transport the comparison along the supplied natural isomorphism of functors. -/
theorem completed_koszul_constant_transport
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (β : completedCechRing T d ≅
      ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true)
    (hβ : ∀ (U : (completedCechSite T)ᵒᵖ) (x : A),
      β.hom.hom.app U ((completedCechScalar T d x).val U) =
        (ConstantCompletion.algebraSection
          (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal) x).val U)
    (F : d.derived T ⥤ ConstantCompletion.D
      (ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true))
    (δ : F ≅ (completedCechDerivedEquiv T d).functor ⋙ ConstantCompletion.dres β.inv)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ) :
    letI := reductionModulesHasDerivedCategory T (d.completedRing T)
    ∃ e : F.obj (DerivedCategory.Q.obj (intrinsicCompletionComplex T d r a C)) ≅
        (ConstantCompletion.completion (completedCechTopology T) A d.ideal true).obj
          (F.obj (DerivedCategory.Q.obj C)),
      F.map (DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a C)) ≫ e.hom =
        (ConstantCompletion.completionUnit (completedCechTopology T) A d.ideal true).app
          (F.obj (DerivedCategory.Q.obj C)) := by
  letI := reductionModulesHasDerivedCategory T (d.completedRing T)
  obtain ⟨e, he⟩ := koszul_to_constant_completion T d β hβ r a ha C
  let H := ConstantCompletion.completion (completedCechTopology T) A d.ideal true
  let κ := ConstantCompletion.completionUnit (completedCechTopology T) A d.ideal true
  refine ⟨δ.app _ ≪≫ e ≪≫ H.mapIso (δ.app _).symm, ?_⟩
  change F.map _ ≫ δ.hom.app _ ≫ e.hom ≫ H.map (δ.inv.app _) = _
  rw [reassoc_of% δ.hom.naturality]
  erw [reassoc_of% he]
  have hn := κ.naturality (δ.hom.app (DerivedCategory.Q.obj C))
  dsimp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hn
  erw [reassoc_of% hn]
  rw [← H.map_comp, δ.hom_inv_id_app, H.map_id, Category.comp_id]

end AlgebraicGeometry.Scheme
