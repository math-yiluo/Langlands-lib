/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import WeilConjectures.AlgebraicGeometry.IntrinsicCompletionCompleted
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.Localization.Pi
import Mathlib.Topology.Separation.DisjointCover
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.FourCorners
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculus
import WeilConjectures.AlgebraicGeometry.StrictTowerOperations
import WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.RingTheory.FactorsThroughLocalization
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
import WeilConjectures.SecSmoothPurity.CochainInverseComparison
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
/-!
# Pullback of strict completed-coefficient towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1261;
Stacks Project, Tag 099N (blueprint: def-weil-pbc-completed-pullback).

The structure map into the completed coefficient ring is built from its finite
projections. It is a morphism, with no invertibility assumption. The functor here
precedes derived inverse limit and acts on every strict derived tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Functor

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- The finite coefficient identification transported by the published constant comparison.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.finiteRingIso {U V : Scheme.{u}} (f : U ⟶ V)
    (n : ℕ) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (d.finiteRing V n) ≅
      d.finiteRing U n :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso
      (pbcLevelConstantComparison V d n).symm ≪≫
    @asIso _ _ _ _ ((proEtaleConstantComparison f).app (d.ringTower.obj (op n)))
      (by exact exchangeConstantComparison_isIso f (A ⧸ d.ideal ^ (n + 1))) ≪≫
    pbcLevelConstantComparison U d n

/-- The finite coefficient comparisons retain every quotient transition.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners).
Proof: the published constants-to-functions comparison commutes with quotient maps.
The constant inverse-image comparison is natural in the finite coefficient ring.
Combining their naturality squares with the limit cone equations gives this equation. -/
theorem AdicCoefficientDatum.integralRingComponent_naturality {U V : Scheme.{u}}
    (f : U ⟶ V) {m n : ℕᵒᵖ} (a : m ⟶ n) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (d.projection V m.unop) ≫
        (d.finiteRingIso f m.unop).hom ≫ (reductionCoefficientSystem U d).map a =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (d.projection V n.unop) ≫
        (d.finiteRingIso f n.unop).hom := by
  let eU := pbcConstantSystemComparison U d
  let eV := pbcConstantSystemComparison V d
  let t : adicLisseRingSystem V d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
      adicLisseRingSystem U d.ideal :=
    NatTrans.ofOpSequence (fun k ↦ (proEtaleConstantComparison f).app
      (CommRingCat.of (A ⧸ d.ideal ^ (k + 1)))) (by
        intro k
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (k + 1))))
  have hn := congrArg (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
    (eV.inv.naturality a)
  have ht := t.naturality a
  have hu := eU.hom.naturality a
  simp only [Functor.map_comp] at hn
  change (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      ((reductionCoefficientSystem V d).map a) ≫
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (pbcLevelConstantComparison V d n.unop).inv =
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (pbcLevelConstantComparison V d m.unop).inv ≫
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((adicLisseRingSystem V d.ideal).map a) at hn
  change (adicLisseRingSystem V d.ideal ⋙
    proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a ≫
      (proEtaleConstantComparison f).app (d.ringTower.obj n) =
    (proEtaleConstantComparison f).app (d.ringTower.obj m) ≫
      (adicLisseRingSystem U d.ideal).map a at ht
  change (adicLisseRingSystem U d.ideal).map a ≫
      (pbcLevelConstantComparison U d n.unop).hom =
    (pbcLevelConstantComparison U d m.unop).hom ≫
      (reductionCoefficientSystem U d).map a at hu
  dsimp only [finiteRingIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    asIso_hom]
  simp only [Category.assoc]
  rw [← hu, ← Category.assoc _ _ ((pbcLevelConstantComparison U d n.unop).hom)]
  rw [← ht]
  simp only [Functor.comp_map, Category.assoc]
  rw [← reassoc_of% hn]
  simp only [← Functor.map_comp_assoc]
  simp only [AdicCoefficientDatum.projection, completedReductionProjection,
    ← Category.assoc, limit.w]

/-- Finite coefficient comparison obtained from constant sections, with its fixed
constant-section normalization. Source: blueprint order 1261
(blueprint: def-weil-pbc-completed-pullback). -/
def completedFiniteCoefficientMap (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        ((pbcAdicRings Y d).obj (op n)) ⟶ (pbcAdicRings X d).obj (op n) :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (pbcLevelConstantComparison Y d n).inv ≫
    proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) ≫
    (pbcLevelConstantComparison X d n).hom

/-- The components of the completed coefficient structure map.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedCoefficientComponent (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ⟶
      (pbcAdicRings X d).obj (op n) :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (pbcAdicProjection Y d n) ≫
    completedFiniteCoefficientMap g d n

/-- The coefficient components form a limit cone.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: the completion projections commute with quotient maps. The finite coefficient
comparison is induced by constant sections, so is natural in the quotient homomorphism.
Apply inverse-image functoriality and these two equalities. -/
theorem completedCoefficientComponent_naturality {b a : ℕᵒᵖ} (f : b ⟶ a) :
    completedCoefficientComponent g d b.unop ≫ (pbcAdicRings X d).map f =
      completedCoefficientComponent g d a.unop := by
  exact d.integralRingComponent_naturality g f

/-- The canonical coefficient structure map into the actual completed limit.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedCoefficientMap :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ⟶
      pbcAdicCompletion X d :=
  limit.lift (pbcAdicRings X d)
    { pt := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d)
      π := { app n := completedCoefficientComponent g d n.unop
             naturality _ _ f := (Category.id_comp _).trans
               (completedCoefficientComponent_naturality g d f).symm } }

open CategoryTheory.Functor

-- Exact-presentation proof utilities from CompletedOpenExchangeTransport.
-- They are private here because that downstream module cannot be imported.
section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance exactTowerFiniteLimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

private instance exactTowerFiniteColimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

end

attribute [-instance] exactTowerFiniteLimits exactTowerFiniteColimits

end AlgebraicGeometry.Scheme
