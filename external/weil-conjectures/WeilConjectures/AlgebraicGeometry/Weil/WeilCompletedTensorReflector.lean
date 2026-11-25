/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
public import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
public import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
public import WeilConjectures.Algebra.Homology.InternalHom
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
public import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
public import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation
public import WeilConjectures.CategoryTheory.RingedKoszulDualizable
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
public import WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic
public import WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
public import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
public import WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower
public import WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
public import WeilConjectures.Algebra.Homology.TelescopeColimit
public import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
public import WeilConjectures.CategoryTheory.RingedAugmentedCechRestriction
public import WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
public import WeilConjectures.CategoryTheory.LocalizationRHom.RingedLocalizationRestrictionSupplement
public import WeilConjectures.Algebra.Homology.SliceTensorNatural
public import WeilConjectures.Algebra.Homology.SliceModuleSheafification
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedCechComparison
import WeilConjectures.CategoryTheory.RingedCechCompletionUnitIdempotence
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.KFlatRHomCurrying
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorDifferential
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomTensorNaturality
import WeilConjectures.CategoryTheory.RingedCechTensorIdempotence
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Tactic.Basic
import WeilConjectures.CategoryTheory.RingedLocalizationFactorTensorAugmentation
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.CategoryTheory.Ringed.RingedLocalizationModelsSupplement
import WeilConjectures.Algebra.Homology.KFlatComparison
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement

/-!
# The Koszul reflector at the actual small pro-etale universes

Source: Stacks Project, Tags 0999, 099B and 0A0E
(blueprint: lem-weil-pbc-ringed-koszul-completion-reflector).
The completed coefficient ring, signed fiber and (u,0) unit are the published ones.

## Main definitions

- `wfCompletionObj`, `wfCompletionUnit`: the published Koszul fiber and its unit.
- `WfCompleteCategory`: the full subcategory with invertible completion unit.
- `wfCompletion`: the functor determined by the reflector's Hom bijection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

/-- A genuine complex representative supplied by essential surjectivity of localization.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
abbrev wfCompletionRepresentative (M : PbcCompletedDerived X d) :=
  DerivedCategory.Q.objPreimage M

/-- The specified Koszul fiber, localized after choosing a representative of this very M.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def wfCompletionObj (M : PbcCompletedDerived X d) : PbcCompletedDerived X d :=
  intrinsicCompletion X d r a ha M (wfCompletionRepresentative X d M)
    (DerivedCategory.Q.objObjPreimageIso M)

/-- Its actual (u,0) unit, including the realization of the chosen representative.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def wfCompletionUnit (M : PbcCompletedDerived X d) : M ⟶ wfCompletionObj X d r a ha M :=
  intrinsicCompletionUnit X d r a ha M (wfCompletionRepresentative X d M)
    (DerivedCategory.Q.objObjPreimageIso M)

/-- Intrinsic completeness, using exactly the published completion predicate.
Source: Stacks 0999 (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def WfIsComplete (M : PbcCompletedDerived X d) : Prop :=
  IsDerivedCompleteIntrinsic X d r a ha M (wfCompletionRepresentative X d M)
    (DerivedCategory.Q.objObjPreimageIso M)

/-- The complete full subcategory has no chosen completion witnesses in its objects.
Source: Stacks 0999 (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
abbrev WfCompleteCategory := ObjectProperty.FullSubcategory (WfIsComplete X d r a ha)

set_option backward.isDefEq.respectTransparency false in
private theorem transportIdempotentUnit {C D : Type*} [Category* C] [Category* D]
    (E : C ≌ D) (F : D ⥤ D) (η : 𝟭 D ⟶ F)
    (h₁ : ∀ M, IsIso (F.map (η.app M)))
    (h₂ : ∀ M, IsIso (η.app (F.obj M)))
    (G : C → C) (ι : ∀ M, M ⟶ G M)
    (e : ∀ M, E.functor.obj (G M) ≅ F.obj (E.functor.obj M))
    (he : ∀ M, E.functor.map (ι M) ≫ (e M).hom = η.app (E.functor.obj M)) :
    (∀ M, IsIso (ι (G M))) ∧
    ∀ M L, IsIso (ι L) → Function.Bijective (fun f : G M ⟶ L ↦ ι M ≫ f) := by
  have hη (M : C) [IsIso (ι M)] : IsIso (η.app (E.functor.obj M)) := by
    rw [← he M]
    infer_instance
  have hmap (M : C) : IsIso (F.map (E.functor.map (ι M))) := by
    have := h₁ (E.functor.obj M)
    have h : IsIso (F.map (E.functor.map (ι M)) ≫ F.map (e M).hom) := by
      rw [← F.map_comp, he M]
      infer_instance
    exact IsIso.of_isIso_comp_right
      (F.map (E.functor.map (ι M))) (F.map (e M).hom)
  constructor
  · intro M
    have := h₂ (E.functor.obj M)
    have hn := η.naturality (e M).hom
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    have : IsIso (η.app (E.functor.obj (G M)) ≫ F.map (e M).hom) := by
      rw [← hn]
      infer_instance
    have : IsIso (η.app (E.functor.obj (G M))) :=
      IsIso.of_isIso_comp_right (η.app (E.functor.obj (G M))) (F.map (e M).hom)
    have : IsIso (E.functor.map (ι (G M)) ≫ (e (G M)).hom) := by
      rw [he]
      infer_instance
    have : IsIso (E.functor.map (ι (G M))) :=
      IsIso.of_isIso_comp_right (E.functor.map (ι (G M))) (e (G M)).hom
    exact isIso_of_reflects_iso _ E.functor
  · intro M L hL
    have := hη L
    constructor
    · intro f g hfg
      have hm := hmap M
      have hfg' : F.map (E.functor.map f) = F.map (E.functor.map g) := by
        apply (cancel_epi (F.map (E.functor.map (ι M)))).mp
        simpa only [← F.map_comp, ← E.functor.map_comp] using
          congrArg (fun h ↦ F.map (E.functor.map h)) hfg
      apply E.functor.map_injective
      apply (cancel_mono (η.app (E.functor.obj L))).mp
      have hn (h : G M ⟶ L) := η.naturality (E.functor.map h)
      dsimp only [Functor.id_map] at hn
      rw [hn f, hn g]
      exact congrArg (fun h ↦ η.app (E.functor.obj (G M)) ≫ h) hfg'
    · intro f
      refine ⟨E.functor.preimage
        ((e M).hom ≫ F.map (E.functor.map f) ≫ inv (η.app (E.functor.obj L))), ?_⟩
      apply E.functor.map_injective
      rw [E.functor.map_comp, E.functor.map_preimage, ← Category.assoc, he]
      have hn := η.naturality (E.functor.map f)
      dsimp only [Functor.id_map] at hn
      rw [← Category.assoc, ← hn]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The published Koszul fiber is the reflector, also with distinct site object/Hom sizes.
Source: Stacks 099B and 0A0E
(blueprint: lem-weil-pbc-ringed-koszul-completion-reflector).
Proof: pass to a small model of the site in the coefficient universe. The site equivalence
preserves module tensor, strict towers and their derived inverse limits. Apply the ringed
Koszul reflector there. Exact countable products on the small pro-etale site identify its
strict derived limit with the published product/mapping-fiber complex. The comparison
preserves the degree-zero augmentation, hence precisely the (u,0) unit. Transport back.
The reflector's complete-output and Hom-bijection assertions give the two clauses. -/
theorem wfCompletionReflector :
    (∀ M : PbcCompletedDerived X d,
      WfIsComplete X d r a ha (wfCompletionObj X d r a ha M)) ∧
    ∀ (M L : PbcCompletedDerived X d), WfIsComplete X d r a ha L →
      Function.Bijective (fun f : wfCompletionObj X d r a ha M ⟶ L ↦
        wfCompletionUnit X d r a ha M ≫ f) := by
  classical
  let O := completedCechRing X d
  let E := completedCechDerivedEquiv X d
  let b := fun i ↦ completedCechScalar X d (a i)
  let F := ringedCechCompletionFunctor O (ringedExtendedCech O r b).1
  let η : 𝟭 _ ⟶ F :=
    { app := ringedCechCompletionUnit O (ringedExtendedCech O r b).1
        (ringedExtendedCech O r b).2
      naturality := by
        intro M N f
        exact (completion_unit_natural O _ _ M N f).symm }
  have hc (M : PbcCompletedDerived X d) :
      ∃ e : E.functor.obj (wfCompletionObj X d r a ha M) ≅ F.obj (E.functor.obj M),
        E.functor.map (wfCompletionUnit X d r a ha M) ≫ e.hom =
          η.app (E.functor.obj M) := by
    let C := wfCompletionRepresentative X d M
    let real := DerivedCategory.Q.objObjPreimageIso M
    obtain ⟨e, he⟩ := completed_fiber_cech_comparison X d r a C
    refine ⟨e ≪≫ F.mapIso (E.functor.mapIso real), ?_⟩
    change E.functor.map (real.inv ≫ _) ≫ _ = _
    rw [E.functor.map_comp]
    dsimp only [Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, ← Category.assoc _ e.hom, he]
    have hn := η.naturality (E.functor.map real.hom)
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    change E.functor.map real.inv ≫ (η.app _ ≫ F.map (E.functor.map real.hom)) = _
    rw [← hn, ← Category.assoc, ← E.functor.map_comp, real.inv_hom_id]
    simp only [E.functor.map_id, Category.id_comp]
  choose e he using hc
  exact transportIdempotentUnit E F η
    (fun M ↦ (ringed_cech_completion_unit_idempotence O r b M).1)
    (fun M ↦ (ringed_cech_completion_unit_idempotence O r b M).2)
    (wfCompletionObj X d r a ha) (wfCompletionUnit X d r a ha) e he

/-- The complete object defined by the explicit Koszul fiber.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def wfCompleteObj (M : PbcCompletedDerived X d) : WfCompleteCategory X d r a ha :=
  ⟨wfCompletionObj X d r a ha M, (wfCompletionReflector X d r a ha).1 M⟩

/-- Unique extension across the actual completion unit, rather than a chosen arbitrary map.
Source: Stacks 099B (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def wfCompletionExtend (M : PbcCompletedDerived X d)
    (L : WfCompleteCategory X d r a ha) (f : M ⟶ L.obj) :
    wfCompletionObj X d r a ha M ⟶ L.obj :=
  Equiv.ofBijective _ ((wfCompletionReflector X d r a ha).2 M L.obj L.property) |>.symm f

set_option backward.isDefEq.respectTransparency false in
/-- The unique extended maps preserve identities and composition.
Source: Stacks 099B (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector).
Proof: compose with the completion unit. Both identity candidates become the same unit;
both composition candidates become f followed by g followed by the final unit. The Hom
bijection's injectivity gives both equations. -/
theorem wfCompletionMap_laws :
    (∀ M : PbcCompletedDerived X d,
      wfCompletionExtend X d r a ha M (wfCompleteObj X d r a ha M)
        (𝟙 M ≫ wfCompletionUnit X d r a ha M) = 𝟙 _) ∧
    ∀ (M N P : PbcCompletedDerived X d) (f : M ⟶ N) (g : N ⟶ P),
      wfCompletionExtend X d r a ha M (wfCompleteObj X d r a ha P)
          ((f ≫ g) ≫ wfCompletionUnit X d r a ha P) =
        wfCompletionExtend X d r a ha M (wfCompleteObj X d r a ha N)
            (f ≫ wfCompletionUnit X d r a ha N) ≫
          wfCompletionExtend X d r a ha N (wfCompleteObj X d r a ha P)
            (g ≫ wfCompletionUnit X d r a ha P) := by
  have hext (M : PbcCompletedDerived X d) (L : WfCompleteCategory X d r a ha)
      (f : M ⟶ L.obj) :
      wfCompletionUnit X d r a ha M ≫ wfCompletionExtend X d r a ha M L f = f := by
    exact (Equiv.ofBijective _
      ((wfCompletionReflector X d r a ha).2 M L.obj L.property)).apply_symm_apply f
  constructor
  · intro M
    apply ((wfCompletionReflector X d r a ha).2 M
      (wfCompletionObj X d r a ha M) ((wfCompletionReflector X d r a ha).1 M)).1
    simp only [hext, Category.id_comp, Category.comp_id]
  · intro M N P f g
    apply ((wfCompletionReflector X d r a ha).2 M
      (wfCompletionObj X d r a ha P) ((wfCompletionReflector X d r a ha).1 P)).1
    dsimp only
    rw [hext, ← Category.assoc, hext, Category.assoc]
    rw [Category.assoc, hext]

/-- Completion with its canonical morphism action determined by reflection.
Source: Stacks 099B (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def wfCompletion : PbcCompletedDerived X d ⥤ WfCompleteCategory X d r a ha where
  obj := wfCompleteObj X d r a ha
  map {M N} f := ObjectProperty.homMk
    (wfCompletionExtend X d r a ha M (wfCompleteObj X d r a ha N)
      (f ≫ wfCompletionUnit X d r a ha N))
  map_id M := ObjectProperty.hom_ext _ ((wfCompletionMap_laws X d r a ha).1 M)
  map_comp f g := ObjectProperty.hom_ext _
    ((wfCompletionMap_laws X d r a ha).2 _ _ _ f g)

end AlgebraicGeometry.Scheme
