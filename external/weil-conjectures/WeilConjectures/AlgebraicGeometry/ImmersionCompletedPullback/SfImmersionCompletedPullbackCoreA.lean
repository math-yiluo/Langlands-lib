/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
public import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import WeilConjectures.CategoryTheory.ModuleInverseImageAction
public import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
public import WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement

import all WeilConjectures.AlgebraicGeometry.Sf.SfImmersionFiniteNormalization
import all WeilConjectures.SmoothPurity.Sf.SfImmersionRoosNormalization
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionCoherence
import all WeilConjectures.CategoryTheory.ExactTowerAugmentedCounit.ExactTowerAugmentedCounitEvaluation
import all WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import all WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-!
# Ordinary immersion pullback and strict completed pullback

Source: smooth-purity localization, returned proof Step 6; Stacks proetale.tex,
Tags 09AA, 099M and 099N (2),(5)
(blueprint: lem-sf-immersion-completed-pullback-coefficients).

The coefficient identifications below only transport the two published presentations
of the same quotient system. All comparisons are normalized by their quotient maps,
universal derived counits, or the two coordinates of a strict Roos complex.
-/

@[expose] public noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section NormalizationProofs

attribute [-instance] CategoryTheory.ringedConstantTowerAdditive
attribute [-instance] CategoryTheory.strictTowerConstantAdditive
attribute [-instance] CategoryTheory.strictTowerLimitAdditive

attribute [local irreducible] AlgebraicGeometry.Scheme.AdicCoefficients.ringSystem
attribute [local irreducible] CategoryTheory.Limits.limit
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures

namespace AlgebraicGeometry.Scheme
namespace ImmersionCompletedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The unique size-change identification of the actual positive quotient rings.
Source: coefficient identification in localization Step 6
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: quotient induction defines the displayed map and its inverse from ULift.down;
the principal ideal powers correspond under ULift.ringEquiv. The formula on quotient
representatives proves both inverse identities and uniqueness. -/
theorem quotientEquiv_exists (n : ℕ) :
    ∃! e : PbcQuotient (pbcIntegralDatum l E) n ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
      ∀ a : PbcIntegralRing l E,
        e (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)) a) =
          ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down) := by
  let e : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E :=
    ULift.ringEquiv
  have hI : Padic.coefficientExtensionIdeal l E (n + 1) =
      Ideal.map e.toRingHom ((pbcIntegralDatum l E).ideal ^ (n + 1)) := by
    simp [pbcIntegralDatum, Padic.coefficientExtensionIdeal, Ideal.map_pow,
      Ideal.map_span, Set.image_singleton, e, pbcUniformizer]
    rfl
  let q := (Ideal.quotientEquiv _ _ e hI).trans ULift.ringEquiv.symm
  refine ⟨q, ?_, ?_⟩
  · intro a
    rfl
  · intro q' hq'
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hq' a

/-- Canonical quotient size transport, fixed on every quotient representative.
Source: localization Step 6
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def quotientEquiv (n : ℕ) := (quotientEquiv_exists l E n).exists.choose

/-- Canonical finite coefficient sheaf identification, retaining commutativity.
Source: localization Step 6, finite projections
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def finiteRingIso (T : Scheme.{u}) (n : ℕ) :
    (pbcAdicRings T (pbcIntegralDatum l E)).obj (op n) ≅
      integralCoefficientCommRingSheaf l E T n :=
  (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).symm ≪≫
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso
      (quotientEquiv l E n).toCommRingCatIso

/-- The two completed rings have the unique identification with these finite projections.
Source: localization Step 6, coefficient inverse-image normalization
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: the finiteRingIso maps intertwine every quotient homomorphism, by quotient
induction. Their limits give the isomorphism. The limit projections are jointly
monic, proving the displayed normalization and uniqueness. -/
theorem completedRingIso_exists (T : Scheme.{u}) :
    ∃! e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E T,
      ∀ n : ℕ, e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
        pbcAdicProjection T (pbcIntegralDatum l E) n ≫ (finiteRingIso l E T n).hom := by
  obtain ⟨_, h⟩ := (IntegralCoefficientPresentation.comparison l E T).2.2.2
  exact (h (quotientEquiv l E)
    (fun n ↦ (quotientEquiv_exists l E n).exists.choose_spec)).2.2.1

/-- The projection-normalized identification of the two completed coefficient sheaves.
Source: localization Step 6
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def completedRingIso (T : Scheme.{u}) := (completedRingIso_exists l E T).exists.choose

/-- Exact coefficient transport to the recorded integral module category.
Source: localization Step 6, completed coefficients
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev transport (T : Scheme.{u}) :
    PbcCompletedDerived T (pbcIntegralDatum l E) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E T) :=
  pbcDerivedRestrict (completedRingIso l E T).inv

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

private theorem moduleFunctor_eq :
    pbcActualModulePull f (pbcIntegralDatum l E) =
      proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f) := by
  exact completedModulePullback_eq_exact f (pbcIntegralDatum l E)

/-- Equality of the two specified ordinary tensor-pullback objects.
Source: localization Step 6, Step 1; Stacks 03EK
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: the canonical exact-pullback theorem identifies the full module functors.
Evaluating that functor equality at M gives the displayed object equality. -/
theorem moduleObj_eq (M : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :
    (pbcActualModulePull f (pbcIntegralDatum l E)).obj M =
      (proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f)).obj M := by
  exact CategoryTheory.Functor.congr_obj (moduleFunctor_eq l E f) M

/-- The object identifications intertwine the actual tensor maps.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: both maps act as identity on the coefficient tensor factor and as inverse
image of the supplied arrow on the module factor; tensor generators give equality. -/
theorem moduleObj_eq_naturality
    {M N : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))} (a : M ⟶ N) :
    (pbcActualModulePull f (pbcIntegralDatum l E)).map a ≫
        eqToHom (moduleObj_eq l E f N) =
      eqToHom (moduleObj_eq l E f M) ≫
        (proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f)).map a := by
  have h := moduleFunctor_eq l E f
  simpa only [eqToIso.hom, eqToHom_app] using (eqToIso h).hom.naturality a

/-- The identity-on-tensor-data ordinary pullback identification.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def moduleIso : pbcActualModulePull f (pbcIntegralDatum l E) ≅
    proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f) :=
  NatIso.ofComponents (fun M ↦ eqToIso (moduleObj_eq l E f M))
    (fun a ↦ moduleObj_eq_naturality l E f a)

/-- Exact descent is the ordinary left derived pullback with its original counit.
Source: localization Step 6, Step 1; Stacks 06YY
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: exact inverse image sends every quasi-isomorphism to a quasi-isomorphism.
On a K-flat representative both counits identify the same termwise tensor complex,
through moduleIso. The universal left-derived property extends this equation
uniquely and supplies an inverse on every object. -/
theorem derivedIso_exists :
    ∃! e : pbcActualDerivedPull f (pbcIntegralDatum l E) ≅
        (pbcIntegralDatum.{u} l E).pull.{u} f,
      whiskerLeft DerivedCategory.Qh e.hom ≫
          (proEtaleRingModulePullback f _ _
            ((pbcIntegralDatum l E).integralRingIso f)).mapDerivedCategoryFactorsh.hom =
        pbcActualPullCounit f (pbcIntegralDatum l E) ≫
          whiskerRight (NatTrans.mapHomotopyCategory (moduleIso l E f).hom (.up ℤ))
            DerivedCategory.Qh := by
  have : (pbcActualDerivedPull f (pbcIntegralDatum l E)).IsLeftDerivedFunctor
      (pbcActualPullCounit f (pbcIntegralDatum l E))
      (HomotopyCategory.quasiIso
        (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) (.up ℤ)) := by
    change (completedOrdinaryPullback f (pbcIntegralDatum l E)).IsLeftDerivedFunctor
      (completedOrdinaryPullbackCounit f (pbcIntegralDatum l E)) _
    infer_instance
  exact exact_left_derived_iso _ _ _ _ (moduleIso l E f)

/-- The counit-normalized comparison Lu* = u*, with u* computed termwise.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def derivedIso := (derivedIso_exists l E f).exists.choose

/-- The canonical finite-ring-linear tensor comparison, transported to the actual Lu*.
Source: localization Step 6, Step 2
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def finiteComparison (n : ℕ) :
    (pbcIntegralDatum l E).reduction X n ⋙ (pbcIntegralDatum l E).finitePull f n ≅
      pbcActualDerivedPull f (pbcIntegralDatum l E) ⋙ (pbcIntegralDatum l E).reduction Y n :=
  (pbcIntegralDatum l E).chi f n ≪≫
    isoWhiskerRight (derivedIso l E f).symm ((pbcIntegralDatum l E).reduction Y n)

/-- A reduction with its completed scalar action retained.
Source: localization Step 6, Step 2
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev restrictedReduction (T : Scheme.{u}) (n : ℕ) :=
  (pbcIntegralDatum l E).reduction T n ⋙
    pbcDerivedRestrict ((pbcIntegralDatum l E).projection T n)

/-- The canonical tensor-unit map to a finite reduction.
Source: localization Step 6, Step 2
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def reductionUnit (T : Scheme.{u}) (n : ℕ) :=
  (pbcDerivedScalarAdjunction ((pbcIntegralDatum l E).projection T n)).unit

/-- All quotient transitions, including equal indices and successive quotients.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def reductionTransition (T : Scheme.{u}) (b a : ℕ) (h : a ≤ b)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (restrictedReduction l E T b).obj K ⟶ (restrictedReduction l E T a).obj K :=
  (pbcDerivedRestrict (pbcAdicProjection T (pbcIntegralDatum l E) b)).map
      (pbcReductionTransition (pbcAdicProjection T (pbcIntegralDatum l E) b)
        (pbcAdicQuotient T (pbcIntegralDatum l E) b a h)
        (pbcAdicProjection T (pbcIntegralDatum l E) a)
        (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a h) K) ≫
    (pbcDerivedRestrictComp (pbcAdicProjection T (pbcIntegralDatum l E) b)
      (pbcAdicQuotient T (pbcIntegralDatum l E) b a h)
      (pbcAdicProjection T (pbcIntegralDatum l E) a)
      (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a h)).hom.app
        (((pbcIntegralDatum l E).reduction T a).obj K)

/-- Restrict the canonical finite-ring-linear comparison to completed coefficients.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def restrictedComparison (n : ℕ) :
    restrictedReduction l E X n ⋙ (pbcIntegralDatum l E).pull f ≅
      (pbcIntegralDatum l E).pull f ⋙ restrictedReduction l E Y n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft ((pbcIntegralDatum l E).reduction X n)
      (proEtaleRingRestrictionDerivedPullback f _ _ _ _
        ((pbcIntegralDatum l E).projection X n) ((pbcIntegralDatum l E).projection Y n)
        ((pbcIntegralDatum l E).integralRingIso f)
        ((pbcIntegralDatum l E).finiteRingIso f n)
        ((pbcIntegralDatum l E).projection_comm f n)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((pbcIntegralDatum l E).chi f n)
      (pbcDerivedRestrict ((pbcIntegralDatum l E).projection Y n)) ≪≫
    Functor.associator _ _ _

attribute [local irreducible] pbcIntegralDatum

attribute [local irreducible] reductionChange reductionDerivedChange
attribute [local irreducible] Functor.mapHomotopyCategory
attribute [local irreducible] Functor.mapHomotopyCategoryFactors
attribute [local irreducible] completedReductionModuleTowerFunctor completedReductionTower
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors
attribute [local irreducible] Functor.mapDerivedCategoryFactorsh

/-- Evaluation of tower pullback is ordinary pullback of the evaluated tower.
Source: localization Step 6, Step 2
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: whiskering and evaluation have identical objects and maps. Functor
extensionality identifies these functors, including their structural proofs. -/
theorem moduleTowerEvaluation_eq (n : ℕ) :
    (pbcIntegralDatum l E).towerModulePull f ⋙
        reductionTowerEvaluation Y
          (reductionModuleRing Y ((pbcIntegralDatum l E).completedRing Y)) n =
      reductionTowerEvaluation X
        (reductionModuleRing X ((pbcIntegralDatum l E).completedRing X)) n ⋙
        proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f) := by
  rfl

/-- Derive the identity-on-levels evaluation comparison.
Source: localization Step 6, Step 2
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def towerEvaluationIso (n : ℕ) :=
  (Functor.mapDerivedCategoryCompIso ((pbcIntegralDatum l E).towerModulePull f)
    (reductionTowerEvaluation Y
      (reductionModuleRing Y ((pbcIntegralDatum l E).completedRing Y)) n)) ≪≫
    Functor.mapDerivedCategoryNatIso (eqToIso (moduleTowerEvaluation_eq l E f n)) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (reductionTowerEvaluation X
        (reductionModuleRing X ((pbcIntegralDatum l E).completedRing X)) n)
      (proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f))).symm

/-- The actual finite projection from the pulled-back strict quotient tower limit.
Source: localization Step 6, Steps 4 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def completedProjection
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) :
    ((pbcIntegralDatum l E).completedPull f).obj K ⟶
      ((pbcIntegralDatum l E).pull f).obj ((restrictedReduction l E X n).obj K) :=
  (completedRlimProjection Y ((pbcIntegralDatum l E).completedRing Y) n).app
      (((pbcIntegralDatum l E).towerPull f).obj
        ((completedReductionTower X (pbcIntegralDatum l E)).obj K)) ≫
    (towerEvaluationIso l E f n).hom.app
      ((completedReductionTower X (pbcIntegralDatum l E)).obj K) ≫
    ((pbcIntegralDatum l E).pull f).map
      ((completedReductionEvaluation X (pbcIntegralDatum l E) n).app K)

private theorem ordinary_transport_eq :
    cbcDatumOrdinaryTransport (pbcIntegralDatum l E) f = derivedIso l E f := by
  symm
  apply (cbcDatumOrdinaryTransport_exists (pbcIntegralDatum l E) f).unique
  · have hμ : moduleIso l E f =
        eqToIso (cbcDatumModulePull_eq (pbcIntegralDatum l E) f) := by
      exact component_iso_eqToIso (cbcDatumModulePull_eq (pbcIntegralDatum l E) f)
        (moduleObj_eq l E f) (fun a ↦ moduleObj_eq_naturality l E f a)
    apply normalized_exact_counit (he := cbcDatumModulePull_eq (pbcIntegralDatum l E) f)
    simpa only [← hμ, derivedIso, pbcActualDerivedPull, pbcActualPullCounit] using
      (derivedIso_exists l E f).exists.choose_spec
  · exact (cbcDatumOrdinaryTransport_exists (pbcIntegralDatum l E) f).exists.choose_spec

end ImmersionCompletedPullback
end AlgebraicGeometry.Scheme

end NormalizationProofs
