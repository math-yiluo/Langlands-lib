/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.Residue.ResidueLissePerfectLift
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedLocalPerfectCriterion
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralDetailedFiniteReduction
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FreeModule.PID
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingClassicalGenerator
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtaleTorLocalGlobal
import all WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import all WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
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
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.CategoryTheory.Abelian.RightDerived
import all Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.ProEtaleCoefficients.CoefficientTorFlatModelSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.LeftExact
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import all WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import all Mathlib.Algebra.Homology.ShortComplex.Basic
import all Mathlib.CategoryTheory.Subobject.Limits
import all WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all WeilConjectures.CategoryTheory.RingedSliceExtensionPreservesExact
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import all WeilConjectures.CategoryTheory.RingedSliceExtensionReflectsExact
import all Mathlib.CategoryTheory.Sites.LocallyInjective
import all Mathlib.CategoryTheory.Abelian.Exact
import all WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import all WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import all WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import all WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import all WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.Algebra.Homology.SliceTensorNatural
import all WeilConjectures.Algebra.Homology.SliceModuleSheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Topology.Sheaves.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# Integral stratified perfect characterization

The perfect and finitely presented models below are actual constant-module
realizations extended to the completed coefficient ring. They are restricted to
strata and slice sites with their actual inverse-image coefficient action.

## Main statements

* `integralStratifiedPerfectCharacterization`: the three equivalent conditions.
* `integralStratifiedPerfectClosure`: shifts, cones, truncations and cohomology.
* `integralStratifiedPerfectDetailed`: comparison with the recorded detailed category.

## References

* Bhatt--Scholze, Definition 6.5.1, Proposition 6.6.11 and Proposition 6.8.11(1), (3)
* Bhatt--Scholze, Definition 6.5.1, Proposition 6.6.11 and Proposition 6.8.11(3)
* Bhatt--Scholze, Proposition 6.8.11(3)
* Bhatt--Scholze, Definition 6.5.1 and Proposition 6.8.11(3)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

private theorem perfect_single_pid {A : Type (u + 1)} [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] (N : ModuleCat.{u + 1} A) [Module.Finite A N] :
    @DerivedCategory.IsPerfectRingComplex A _
      (HasDerivedCategory.standard (ModuleCat.{u + 1} A))
      ((DerivedCategory.singleFunctor _ 0).obj N) := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  rw [DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton]
  let P := (ObjectProperty.singleton
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
      (ModuleCat.of A A))).triangEnvelope
  let : (ObjectProperty.singleton
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
      (ModuleCat.of A A))).Nonempty :=
    ⟨_, (ObjectProperty.singleton_iff _ _).mpr rfl⟩
  have : P.IsTriangulated := by
    dsimp [P]
    infer_instance
  have hA : P ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A A)) :=
    ObjectProperty.le_triangEnvelope _ _ ((ObjectProperty.singleton_iff _ _).mpr rfl)
  have hfree (n : ℕ) :
      P ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A (Fin n → A))) := by
    exact P.prop_of_isLimit
      (isLimitOfPreserves (DerivedCategory.singleFunctor _ 0)
        (ModuleCat.productConeIsLimit (fun _ : Fin n ↦ ModuleCat.of A A)))
      (fun _ ↦ hA)
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A N
  have hS := LinearMap.shortExact_shortComplexKer hf
  have : Module.Finite A (LinearMap.ker f) := Module.IsNoetherian.finite A _
  have hker : P ((DerivedCategory.singleFunctor _ 0).obj
      (ModuleCat.of A (LinearMap.ker f))) :=
    P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
      (Module.finBasis A (LinearMap.ker f)).equivFun.toModuleIso.symm) (hfree _)
  exact P.ext_of_isTriangulatedClosed₃ _ hS.singleTriangle_distinguished hker (hfree n)

private theorem integral_pid (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsPrincipalIdealRing (PbcIntegralRing l E) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    h.2.2.2.2.2.2.2.2.1
  exact IsPrincipalIdealRing.of_surjective ULift.ringEquiv.symm
    ULift.ringEquiv.symm.surjective

private theorem perfect_finite_homology {A : Type (u + 1)} [CommRing A]
    [IsNoetherianRing A] (P : completedConstantDerived (ModuleCat.{u + 1} A))
    (hP : @DerivedCategory.IsPerfectRingComplex A _
      (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P) (q : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).obj P) := by
  obtain ⟨C, a, b, -, -, hC, ⟨e⟩⟩ := hP
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).obj P ≅ C.homology q :=
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) q).app C
  have := (hC q).2
  have : Module.Finite A (C.cycles q) :=
    Module.Finite.of_injective (C.iCycles q).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite A (C.homology q) :=
    Module.Finite.of_surjective (C.homologyπ q).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.Finite.equiv eH.toLinearEquiv.symm

private def localRestrictionComparison {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) :
    (ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, u + 2, u + 2}
      ((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)) U).obj
        ((adicTowerPullback g R).obj K) ≅ integralLocalDerived g R U K := by
  let B := (adicLisseForget S).obj ((adicTowerInverseImage g).obj R)
  let F := SheafOfModules.overFunctor.{u + 1} B U
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).2.1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).2.2
  exact F.mapDerivedCategory.mapIso
    (DerivedCategory.Q.objObjPreimageIso ((adicTowerPullback g R).obj K)).symm ≪≫
      F.mapDerivedCategoryFactors.app _

private def localMapIso {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    {K L : DerivedCategory (pbcModules T R)} (e : K ≅ L) :
    integralLocalDerived g R U K ≅ integralLocalDerived g R U L :=
  (localRestrictionComparison g R U K).symm ≪≫
    (ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, u + 2, u + 2}
      ((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)) U).mapIso
        ((adicTowerPullback g R).mapIso e) ≪≫ localRestrictionComparison g R U L

private def localSingleIso {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (M : pbcModules T R) :
    integralLocalDerived g R U ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((SheafOfModules.overFunctor _ U).obj
        ((proEtaleModuleInverseImage g R).obj M)) := by
  let R' := (adicTowerInverseImage g).obj R
  let B := (adicLisseForget S).obj R'
  let F := proEtaleRingModulePullback g R R' (Iso.refl _)
  let G := SheafOfModules.overFunctor.{u + 1} B U
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).2.1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).2.2
  let θ := (SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0}
    (Iso.refl R')).choose
  let e : F.obj M ≅ (proEtaleModuleInverseImage g R).obj M := θ _
  exact (localRestrictionComparison g R U _).symm ≪≫
    G.mapDerivedCategory.mapIso ((F.mapDerivedCategorySingleFunctor 0).app M) ≪≫
      (G.mapDerivedCategorySingleFunctor 0).app (F.obj M) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (G.mapIso e)

private def localHomologyIso {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) (q : ℤ) := by
  let R' := (adicTowerInverseImage g).obj R
  let B := (adicLisseForget S).obj R'
  let F := proEtaleRingModulePullback g R R' (Iso.refl _)
  let G := SheafOfModules.overFunctor.{u + 1} B U
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).2.1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).2.2
  let θ := (SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0}
    (Iso.refl R')).choose
  exact (G.mapIso (θ ((proEtaleModuleInverseImage g R).obj
    ((DerivedCategory.homologyFunctor (pbcModules T R) q).obj K)))).symm ≪≫
    G.mapIso ((F.mapDerivedCategoryHomologyFunctorIso q).app K) ≪≫
      ((G.mapDerivedCategoryHomologyFunctorIso q).app (F.mapDerivedCategory.obj K)) ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso (localRestrictionComparison g R U K)

private theorem perfect_stratified_homology (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (hK : IsIntegralStratifiedPerfect T d K) (q : ℤ) :
    IsIntegralStratifiedFinitelyPresented T d
      ((DerivedCategory.homologyFunctor _ q).obj K) := by
  let : IsNoetherianRing A := d.noetherian
  obtain ⟨s, hs⟩ := hK
  refine ⟨s, fun i ↦ ?_⟩
  obtain ⟨V, hV, hv⟩ := hs i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hv U f hf
  have := perfect_finite_homology P hP q
  let : PreservesFiniteLimits (integralConstantModule T d) :=
    (integralConstantModule_exact T d).1
  let : PreservesFiniteColimits (integralConstantModule T d) :=
    (integralConstantModule_exact T d).2
  let c := ((integralConstantModule T d).mapDerivedCategoryHomologyFunctorIso q).app P
  refine ⟨(DerivedCategory.homologyFunctor _ q).obj P,
    Module.finitePresentation_of_finite A _, ⟨?_⟩⟩
  exact localHomologyIso (s.immersion i) _ U K q ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (localHomologyIso (s.immersion i) _ U ((integralConstantDerived T d).obj P) q).symm ≪≫
        (SheafOfModules.overFunctor _ U).mapIso
          ((proEtaleModuleInverseImage (s.immersion i) _).mapIso c.symm)

private theorem finitelyPresented_single_perfect
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] (d : AdicCoefficientDatum A)
    (M : pbcModules T (pbcAdicCompletion T d))
    (hM : IsIntegralStratifiedFinitelyPresented T d M) :
    IsIntegralStratifiedPerfect T d ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨s, hs⟩ := hM
  refine ⟨s, fun i ↦ ?_⟩
  obtain ⟨V, hV, hv⟩ := hs i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨N, hN, ⟨e⟩⟩ := hv U f hf
  let : Module.FinitePresentation A N := hN
  let : PreservesFiniteLimits (integralConstantModule T d) :=
    (integralConstantModule_exact T d).1
  let : PreservesFiniteColimits (integralConstantModule T d) :=
    (integralConstantModule_exact T d).2
  let c := ((integralConstantModule T d).mapDerivedCategorySingleFunctor 0).app N
  refine ⟨(DerivedCategory.singleFunctor _ 0).obj N, perfect_single_pid N, ⟨?_⟩⟩
  exact localSingleIso (s.immersion i) _ U M ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
      (localSingleIso (s.immersion i) _ U ((integralConstantModule T d).obj N)).symm ≪≫
        localMapIso (s.immersion i) _ U c.symm

private theorem finitelyPresented_iso (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {M N : pbcModules T (pbcAdicCompletion T d)} (e : M ≅ N)
    (hM : IsIntegralStratifiedFinitelyPresented T d M) :
    IsIntegralStratifiedFinitelyPresented T d N := by
  obtain ⟨s, hs⟩ := hM
  refine ⟨s, fun i ↦ ?_⟩
  obtain ⟨V, hV, hv⟩ := hs i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨L, hL, ⟨eL⟩⟩ := hv U f hf
  exact ⟨L, hL, ⟨(SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (s.immersion i) _).mapIso e.symm) ≪≫ eL⟩⟩

private theorem perfect_bounded {A : Type (u + 1)} [CommRing A]
    (P : completedConstantDerived (ModuleCat.{u + 1} A))
    (hP : @DerivedCategory.IsPerfectRingComplex A _
      (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P) :
    DerivedCategory.TStructure.t.bounded P := by
  obtain ⟨C, a, b, ha, hb, -, ⟨e⟩⟩ := hP
  let eH (q : ℤ) : (DerivedCategory.homologyFunctor _ q).obj P ≅ C.homology q :=
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app C
  refine ⟨⟨a, (DerivedCategory.isGE_iff _ a).2 ?_⟩,
    ⟨b, (DerivedCategory.isLE_iff _ b).2 ?_⟩⟩
  · intro q hq
    exact (C.exactAt_of_isGE a q hq).isZero_homology.of_iso (eH q)
  · intro q hq
    exact (C.exactAt_of_isLE b q hq).isZero_homology.of_iso (eH q)

private theorem local_bounded {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) (hK : DerivedCategory.TStructure.t.bounded K) :
    DerivedCategory.TStructure.t.bounded (integralLocalDerived g R U K) := by
  let R' := (adicTowerInverseImage g).obj R
  let B := (adicLisseForget S).obj R'
  let F := proEtaleRingModulePullback g R R' (Iso.refl _)
  let G := SheafOfModules.overFunctor.{u + 1} B U
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).2.1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B U).2.2
  exact DerivedCategory.TStructure.t.bounded.prop_of_iso
    (localRestrictionComparison g R U K)
    (G.bounded_mapDerivedCategory_obj (F.bounded_mapDerivedCategory_obj hK))

attribute [-instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModelUp_isContinuous in
private def commRingInverseImageUnderlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf ((adicLisseForget Y).obj R) ⋙
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} := by
  let e := (proEtaleModelModuleInverseImage_underlying f R).some
  let A := (adicLisseForget Y).obj R
  let B := (adicLisseForget X).obj ((adicTowerInverseImage f).obj R)
  let L := SheafOfModules.pullback.{u + 1} (F := proEtaleModelBaseChange f)
    (J := proEtaleModelTopology Y) (K := proEtaleModelTopology X)
    (proEtaleModelRingUnit f R)
  let La := Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
    AddCommGrpCat.{u + 1} (proEtaleModelTopology Y) (proEtaleModelTopology X)
  let t : proEtaleModuleToModel A ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf A ⋙
        (modelSheafEquivalence Y AddCommGrpCat.{u + 1}).inverse :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  let q : proEtaleModuleFromModel B ⋙ SheafOfModules.toSheaf B ≅
      SheafOfModules.toSheaf _ ⋙
        (modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  exact Functor.isoWhiskerLeft (proEtaleModuleToModel A ⋙ L) q ≪≫
    Functor.isoWhiskerLeft (proEtaleModuleToModel A)
      (Functor.isoWhiskerRight e (modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor) ≪≫
    Functor.isoWhiskerRight t
      (La ⋙ (modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf A) (modelAbelianPullbackIso f)

private theorem stratified_perfect_bounded (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (hK : IsIntegralStratifiedPerfect T d K) : DerivedCategory.TStructure.t.bounded K := by
  classical
  let R := pbcAdicCompletion T d
  obtain ⟨s, hs⟩ := hK
  have hn (i : Fin s.n) : TopologicalSpace.NoetherianSpace (s.domain i) :=
    (s.immersion i).isEmbedding.isInducing.noetherianSpace
  let := hn
  have hc (i : Fin s.n) : CompactSpace (⊤_ (s.domain i).ProEt).left := by
    let X := s.domain i
    have ht : IsTerminal (ProEt.mk (𝟙 X)) :=
      IsTerminal.ofUniqueHom
        (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _) (by trivial)) (by
        intro U f
        apply MorphismProperty.Over.Hom.ext
        have hw := MorphismProperty.Over.w f
        change f.left ≫ 𝟙 X = U.hom at hw
        exact (Category.comp_id _).symm.trans hw)
    let e : (⊤_ X.ProEt).left ≅ X :=
      (ProEt.forget X ⋙ Over.forget X).mapIso (terminalIsTerminal.uniqueUpToIso ht)
    exact QuasiCompact.compactSpace_of_compactSpace e.hom
  let := hc
  choose W hW hw using hs
  choose I hI V f hV hf using
    fun i ↦ ProEt.qc_finite_cover (s.domain i) (⊤_ (s.domain i).ProEt) (W i) (hW i)
  let := hI
  have hb (i : Fin s.n) (j : I i) :
      DerivedCategory.TStructure.t.bounded
        (integralLocalDerived (s.immersion i) R (V i j) K) := by
    obtain ⟨P, hP, ⟨e⟩⟩ := hw i (V i j) (f i j) (hf i j)
    let : PreservesFiniteLimits (integralConstantModule T d) :=
      (integralConstantModule_exact T d).1
    let : PreservesFiniteColimits (integralConstantModule T d) :=
      (integralConstantModule_exact T d).2
    exact DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm
      (local_bounded (s.immersion i) R (V i j) _
        ((integralConstantModule T d).bounded_mapDerivedCategory_obj (perfect_bounded P hP)))
  have hbounds (i : Fin s.n) (j : I i) : ∃ a b : ℤ,
      (integralLocalDerived (s.immersion i) R (V i j) K).IsGE a ∧
        (integralLocalDerived (s.immersion i) R (V i j) K).IsLE b := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb i j
    exact ⟨a, b, ha, hb⟩
  choose a b ha hb using hbounds
  let J := Σ i : Fin s.n, I i
  let : Fintype J := Fintype.ofFinite J
  let a₀ : ℤ := -∑ j : J, |a j.1 j.2|
  let b₀ : ℤ := ∑ j : J, |b j.1 j.2|
  have key (q : ℤ) (hq : q < a₀ ∨ b₀ < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
    let H := (DerivedCategory.homologyFunctor _ q).obj K
    have hstr (i : Fin s.n) :
        IsZero ((proEtaleModuleInverseImage (s.immersion i) R).obj H) := by
      let B := (adicLisseForget (s.domain i)).obj
        ((adicTowerInverseImage (s.immersion i)).obj R)
      have hcV : (ProEt.topology (s.domain i)).CoversTop (V i) :=
        ((ProEt.topology (s.domain i)).coversTop_iff_of_isTerminal
          (⊤_ (s.domain i).ProEt) terminalIsTerminal (V i)).mpr (by
            exact (ProEt.topology (s.domain i)).superset_covering
              (Sieve.ofArrows_le_ofObjects (V i) (f i)) (hV i))
      apply CategoryTheory.isZero_of_slice_cover B (V i) hcV
      intro j
      have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
          (integralLocalDerived (s.immersion i) R (V i j) K)) := by
        rcases hq with hq | hq
        · apply (DerivedCategory.isGE_iff _ (a i j)).1 (ha i j) q
          have hsum := Finset.single_le_sum
            (f := fun j : J ↦ |a j.1 j.2|) (fun _ _ ↦ abs_nonneg _)
            (Finset.mem_univ (⟨i, j⟩ : J))
          dsimp [a₀] at hq
          linarith [neg_abs_le (a i j)]
        · apply (DerivedCategory.isLE_iff _ (b i j)).1 (hb i j) q
          have hsum := Finset.single_le_sum
            (f := fun j : J ↦ |b j.1 j.2|) (fun _ _ ↦ abs_nonneg _)
            (Finset.mem_univ (⟨i, j⟩ : J))
          dsimp [b₀] at hq
          linarith [le_abs_self (b i j)]
      exact hz.of_iso (localHomologyIso (s.immersion i) R (V i j) K q)
    have hz : IsZero ((SheafOfModules.toSheaf ((adicLisseForget T).obj R)).obj H) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp
        s.immersion
      · intro x
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
          (s.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
        exact ⟨i, (s.range_immersion i).symm ▸ hi⟩
      · intro i
        rw [(AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
          (s.immersion i)).map_id]
        have hi := (SheafOfModules.toSheaf _).map_isZero (hstr i)
        exact (hi.of_iso
          ((commRingInverseImageUnderlying (s.immersion i) R).app H).symm).eq_of_src _ _
    apply (IsZero.iff_id_eq_zero H).2
    apply (SheafOfModules.toSheaf ((adicLisseForget T).obj R)).map_injective
    simpa using hz.eq_of_src
      ((SheafOfModules.toSheaf _).map (𝟙 H)) ((SheafOfModules.toSheaf _).map 0)
  exact ⟨⟨a₀, (DerivedCategory.isGE_iff _ _).2 fun q hq ↦ key q (.inl hq)⟩,
    ⟨b₀, (DerivedCategory.isLE_iff _ _).2 fun q hq ↦ key q (.inr hq)⟩⟩

/-- The three descriptions are equivalent. -/
theorem integralStratifiedPerfectCharacterization
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤)))
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))) :
    (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
      IsIntegralStratifiedPerfect T (pbcIntegralDatum l E) K) ∧
    (IsIntegralStratifiedPerfect T (pbcIntegralDatum l E) K ↔
      IsIntegralBoundedConstructibleCohomology T (pbcIntegralDatum l E) K) := by
  let d := pbcIntegralDatum l E
  let : IsPrincipalIdealRing (PbcIntegralRing l E) := integral_pid l E
  let : IsDomain (PbcIntegralRing l E) :=
    (ULift.ringEquiv : PbcIntegralRing l E ≃+*
      Padic.coefficientExtensionIntegers l E).toMulEquiv.isDomain _
  have hc := integralCompletedLocalPerfectCriterion T l E _hdim _hl
  refine ⟨hc K, ⟨?_, ?_⟩⟩
  · intro hK
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := stratified_perfect_bounded T d K hK
    let : K.IsGE a := ha
    refine ⟨⟨min a b, b, min_le_right _ _, ?_, hb⟩,
      fun q ↦ perfect_stratified_homology T d K hK q⟩
    exact DerivedCategory.TStructure.t.isGE_of_ge K (min a b) a (min_le_left _ _)
  · intro hK
    let P : ObjectProperty (DerivedCategory (pbcModules T (pbcAdicCompletion T d))) :=
      PbcIsBoundedConstructibleComplete T d
    let Q : ObjectProperty (pbcModules T (pbcAdicCompletion T d)) :=
      IsIntegralStratifiedFinitelyPresented T d
    have hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t) := by
      intro t
      simpa only [map_natCast] using
        RingHom.isUnit_map (T.presheaf.germ ⊤ t trivial).hom _hl
    have hP := pbcIntegralUniformComplete_isTriangulated l E T _hdim hInv
    let : P.IsClosedUnderIsomorphisms := hP.1
    let : P.IsTriangulated := hP.2
    let : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ finitelyPresented_iso T d e h⟩
    apply (hc K).mp
    apply DerivedCategory.prop_of_bounded P Q
      (fun M hM ↦ (hc _).mpr (finitelyPresented_single_perfect T d M hM)) K
    · obtain ⟨a, b, -, ha, hb⟩ := hK.1
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    · exact hK.2

/-- Closure under all shifts, ambient cones, standard truncations and cohomology in
degree zero. -/
theorem integralStratifiedPerfectClosure
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤))) :
    (∀ K, PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K →
      ∀ n : ℤ, PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        ((shiftFunctor _ n).obj K)) ∧
    (∀ Δ : Triangle
      (DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))),
      Δ ∈ distTriang _ → PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) Δ.obj₁ →
        PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) Δ.obj₂ →
        PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) Δ.obj₃) ∧
    (∀ K, PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K → ∀ n : ℤ,
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (∀ K, PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K → ∀ q : ℤ,
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) := by
  have hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t) := by
    intro t
    simpa only [map_natCast] using
      RingHom.isUnit_map (T.presheaf.germ ⊤ t trivial).hom _hl
  have h := pbcIntegralUniformComplete_isTriangulated l E T _hdim hInv
  let : ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) := h.2
  let : ObjectProperty.IsClosedUnderIsomorphisms
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) := h.1
  refine ⟨?_, ?_, ?_⟩
  · intro K hK n
    exact ObjectProperty.le_shift
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) n K hK
  · intro Δ hΔ h₁ h₂
    exact ObjectProperty.ext_of_isTriangulatedClosed₃
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) Δ hΔ h₁ h₂
  · let Q : ObjectProperty (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) :=
      IsIntegralStratifiedFinitelyPresented T (pbcIntegralDatum l E)
    have : Q.IsClosedUnderIsomorphisms := ⟨by
      rintro F G e ⟨s, hs⟩
      refine ⟨s, fun i ↦ ?_⟩
      obtain ⟨V, hV, hlocal⟩ := hs i
      refine ⟨V, hV, fun U f hf ↦ ?_⟩
      obtain ⟨N, hN, ⟨eN⟩⟩ := hlocal U f hf
      exact ⟨N, hN, ⟨((SheafOfModules.overFunctor _ U).mapIso
        ((proEtaleModuleInverseImage (s.immersion i)
          (pbcAdicCompletion T (pbcIntegralDatum l E))).mapIso e)).symm ≪≫ eN⟩⟩⟩
    have criterion (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
        PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
          IsIntegralBoundedConstructibleCohomology T (pbcIntegralDatum l E) K := by
      have hchar := integralStratifiedPerfectCharacterization T l E _hdim _hl K
      exact hchar.1.trans hchar.2
    constructor
    · intro K hK n
      obtain ⟨⟨a, b, hab, ha, hb⟩, hcoh⟩ := (criterion K).mp hK
      have : Q.ContainsZero := ⟨_, DerivedCategory.isZero_of_isLE K b (b + 1) (by omega),
        hcoh (b + 1)⟩
      have hQ : DerivedCategory.homologyProperty Q K := hcoh
      constructor
      · apply (criterion _).mpr
        exact ⟨⟨a, b, hab, inferInstance, inferInstance⟩,
          DerivedCategory.homologyProperty_truncLE hQ n⟩
      · apply (criterion _).mpr
        exact ⟨⟨a, b, hab, inferInstance, inferInstance⟩,
          DerivedCategory.homologyProperty_truncGE hQ n⟩
    · intro K hK q
      obtain ⟨⟨a, b, _, ha, hb⟩, hcoh⟩ := (criterion K).mp hK
      have : Q.ContainsZero := ⟨_, DerivedCategory.isZero_of_isLE K b (b + 1) (by omega),
        hcoh (b + 1)⟩
      apply (criterion _).mpr
      refine ⟨⟨0, 0, le_rfl, inferInstance, inferInstance⟩, fun r ↦ ?_⟩
      change Q _
      by_cases hr : r = 0
      · subst r
        exact Q.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
          ((DerivedCategory.homologyFunctor _ q).obj K)).symm (hcoh q)
      · apply Q.prop_of_isZero
        rcases lt_or_gt_of_ne hr with hr | hr
        · exact DerivedCategory.isZero_of_isGE _ 0 r hr
        · exact DerivedCategory.isZero_of_isLE _ 0 r hr

/-- The same conditions describe precisely the detailed integral category under
its own coefficient hypotheses. The comparison is fixed by all quotient projections,
so it compares the same completed ring and reduction functors. -/
theorem integralStratifiedPerfectDetailed
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [IsNoetherian T] (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hinv : IsUnit (l : Γ(T, ⊤)))
    (K : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T)) :
    WeilConjectures.sfIntegralConstructible l E T K ↔
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        ((integralDetailedTransport T l E).obj K) := by
  let L := (integralDetailedTransport T l E).obj K
  have hc := WeilConjectures.purDetailedTransport_complete_iff l E T K
  have hr := pbcUniformReductionCriterion l E T L
  constructor
  · rintro ⟨hcomplete, a, b, _hab, hred⟩
    refine ⟨hc.mp hcomplete, hr.mpr ?_⟩
    exact ⟨a, b, fun n ↦ (integralDetailedFiniteReduction T l E K n a b).mp (hred n)⟩
  · rintro ⟨hcomplete, hmodels⟩
    obtain ⟨a, b, hred⟩ := hr.mp hmodels
    refine ⟨hc.mpr hcomplete, min a b, b, min_le_right _ _, fun n ↦ ?_⟩
    apply (integralDetailedFiniteReduction T l E K n (min a b) b).mpr
    have := (hred n).1
    exact ⟨DerivedCategory.TStructure.t.isGE_of_ge _ (min a b) a (min_le_left _ _),
      (hred n).2⟩

end AlgebraicGeometry.Scheme
