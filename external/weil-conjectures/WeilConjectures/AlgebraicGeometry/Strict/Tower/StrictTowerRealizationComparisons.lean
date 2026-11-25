/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.Compactification.BaseChange

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Basic.Denumerable
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenEndpointLimitTransport
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import all WeilConjectures.CategoryTheory.Strict.StrictRoosShiftLocalization
import all WeilConjectures.CategoryTheory.NormalizedLimitSquare.NormalizedLimitSquareCoherence
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import all WeilConjectures.CategoryTheory.StrictRoosComparison
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.StrictRoosNormalization
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import all Mathlib.Basic.Denumerable
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import all WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenScalarLimitCoherence
import WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProducts
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
import all WeilConjectures.AlgebraicGeometry.RelativeCompactSupport.RelativeCompactSupportPasting
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingRestrictionSquare

/-!
# Canonical comparisons for strict-tower realization

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
Definition 1939 and the proof of proposition-composition-base-change-rf-shriek--4; Stacks 03DI,
09BP, 0A07 (blueprint: def-cbc-strict-tower-realization-comparisons).

All comparisons below are adjunction mates or their exact derived transports.
The strict composite is constructed before applying either Rlim or evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Finish proof checking before the final axiom scan.
set_option Elab.async false
-- Avoid repeatedly traversing the large dependent normalized-comparison interfaces.
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.StrictTower
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory proEtaleRingModulePullback proEtaleRingModuleAdjunction

attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Constant-tower/Rlim adjunction for an arbitrary coefficient sheaf.
Source: Stacks 079P (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationLimitAdj (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _).mapDerivedCategory ⊣ completedRlim T R :=
  (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _) ⊣
    completedTowerLimit T R).mapDerivedCategoryRightDerivedAdjunction

/-- Exact transport of the identity constant-diagram comparison.
Source: Stacks 079P (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationConst {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ).mapDerivedCategory ≅
      (Functor.const ℕᵒᵖ).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The canonical limit comparison, defined by the constant-diagram mate.
This definition fixes its value on resolutions and on strict augmentations.
Source: Stacks 09BP, 0A07
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationLimitMap {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    completedRlim T R ⋙ F.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory ⋙ completedRlim S R' :=
  mateEquiv (cbcRealizationLimitAdj T R) (cbcRealizationLimitAdj S R')
    (cbcRealizationConst F).hom

section LimitMateNormalization

-- Unit-normalized Roos comparison, following the existing endpoint proof
-- (Stacks 09BP, 0941; lem-cbc-completed-open-endpoint-limit-transport).
private def cbcRealizationCochainUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  derivedCochainRightUnit (completedTowerLimit T R) (completedRlim T R)
    (completedRlimUnit T R)

private theorem cbcRealizationCochainUnit_eq (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (X : CochainComplex (ℕᵒᵖ ⥤ reductionModules T R) ℤ) :
    (cbcRealizationCochainUnit T R).app X = exchangeDerivedUnit (completedTowerLimit T R) X := by
  unfold cbcRealizationCochainUnit
  rw [cochainRightUnit_app_eq]
  dsimp only [exchangeDerivedUnit]
  simp only [quotient_hom_id, quotient_inv_id, Category.id_comp]
  erw [(completedTowerLimit T R).rightDerivedFunctor.map_id, Category.comp_id]
  rfl

private def cbcRealizationRoosUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ completedRlim T R :=
  (Functor.isoWhiskerRight
    (CategoryTheory.StrictRoosShiftProof.limitModelIso (A := reductionModules T R))
    DerivedCategory.Q).inv ≫ cbcRealizationCochainUnit T R

private theorem cbcRealizationRoosUnit_derived (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (completedRlim T R).IsRightDerivedFunctor (cbcRealizationRoosUnit T R)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ reductionModules T R) (.up ℤ)) := by
  have : (completedRlim T R).IsRightDerivedFunctor (completedRlimUnit T R)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
    dsimp only [completedRlim, completedRlimUnit]
    infer_instance
  have h := cochainRightUnit_universal (completedTowerLimit T R) (completedRlim T R)
    (completedRlimUnit T R)
  apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).mpr
  exact (Functor.isLeftKanExtension_iff_of_iso₂
    (cbcRealizationCochainUnit T R) (cbcRealizationRoosUnit T R)
    (Functor.isoWhiskerRight
      (CategoryTheory.StrictRoosShiftProof.limitModelIso (A := reductionModules T R))
      DerivedCategory.Q) (Iso.refl _) (by
        dsimp only [cbcRealizationRoosUnit, Iso.refl_hom]
        rw [Functor.whiskerLeft_id', Category.comp_id,
          ← Category.assoc, Iso.hom_inv_id, Category.id_comp])).mp h

private theorem cbcRealizationRoos_normalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasLimits C] [HasLimits D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape ℕᵒᵖ F]
    (LA : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory C)
    (LB : DerivedCategory (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory D)
    (uA : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA)
    (uB : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB)
    (hnorm : CbcLimitNormalized F LA LB
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uA)
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uB) lambda) :
    ∀ X : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      F.mapDerivedCategory.map (uA.app X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((cbcTowerFactors F).hom.app X) =
      F.mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (preservesLimitNatIso F (J := ℕᵒᵖ)) (.up ℤ)).hom.app X) ≫
        uB.app ((((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex
          (.up ℤ)).obj X) := by
  let tau := preservesLimitNatIso F (J := ℕᵒᵖ)
  intro X
  let Y :=
    (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (.up ℤ)).obj X
  let iA := CategoryTheory.StrictRoosShiftProof.limitModelPointIso X
  let iB := CategoryTheory.StrictRoosShiftProof.limitModelPointIso Y
  let beta := limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone
    (limit.cone X.asFunctor))
  have hi : (F.mapHomologicalComplex (.up ℤ)).map iA.hom ≫ beta =
      (NatIso.mapHomologicalComplex tau (.up ℤ)).hom.app X ≫ iB.hom := by
    apply limit.hom_ext
    intro n
    dsimp only [beta]
    rw [Category.assoc, limit.lift_π]
    dsimp only [Functor.mapCone, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    erw [← Functor.map_comp,
      CategoryTheory.StrictRoosShiftProof.limitModelPointIso_hom_π,
      Category.assoc, CategoryTheory.StrictRoosShiftProof.limitModelPointIso_hom_π]
    apply HomologicalComplex.Hom.ext
    funext q
    change F.map (limit.π (X.X q) n) =
      (preservesLimitIso F (X.X q)).hom ≫ limit.π _ n
    exact (preservesLimitIso_hom_π F (X.X q) n).symm
  have hh := congrArg (fun z ↦ F.mapDerivedCategory.map (DerivedCategory.Q.map iA.hom) ≫ z)
    (hnorm.equation X)
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc, Functor.map_comp] at hh
  change F.mapDerivedCategory.map (DerivedCategory.Q.map iA.hom) ≫
    F.mapDerivedCategory.map (DerivedCategory.Q.map iA.inv) ≫ _ = _ at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  erw [F.mapDerivedCategoryFactors_hom_naturality_assoc] at hh
  simp only [← DerivedCategory.Q.map_comp_assoc] at hh
  erw [reassoc_of% hi] at hh
  change _ = _ ≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex tau (.up ℤ)).hom.app X ≫ iB.hom ≫ iB.inv) ≫ _ at hh
  simp only [Iso.hom_inv_id, Category.comp_id] at hh
  exact hh

private theorem cbcRealizationLimit_cochain_normalized
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasLimits C] [HasLimits D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
    [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive] [(lim : (ℕᵒᵖ ⥤ D) ⥤ D).Additive]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape ℕᵒᵖ F]
    (uA : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor)
    (uB : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor)
    (hA : ∀ X, uA.app X = exchangeDerivedUnit (lim : (ℕᵒᵖ ⥤ C) ⥤ C) X)
    (hB : ∀ X, uB.app X = exchangeDerivedUnit (lim : (ℕᵒᵖ ⥤ D) ⥤ D) X)
    (lambda : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      cbcTowerDerived F ⋙ (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor)
    (hnorm : CbcLimitNormalized F
      (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor
      (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uA)
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uB) lambda) :
    ExchangeDerivedPushNormalized (lim : (ℕᵒᵖ ⥤ C) ⥤ C)
      (lim : (ℕᵒᵖ ⥤ D) ⥤ D) F ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)
      (preservesLimitNatIso F (J := ℕᵒᵖ)) lambda := by
  have h := cbcRealizationRoos_normalization F
    (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor
    (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor uA uB lambda hnorm
  intro X
  simpa only [hA, hB] using h X

-- Check the ordinary constant/limit mate before specializing coefficient categories.
private theorem cbcRealizationOrdinaryLimitMate
    {C D : Type*} [Category C] [Category D] [HasLimits C] [HasLimits D]
    (F : C ⥤ D) [PreservesLimitsOfShape ℕᵒᵖ F] :
    (mateEquiv (constLimAdj : (Functor.const ℕᵒᵖ : C ⥤ _) ⊣ lim)
      (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim)
      (TwoSquare.mk _ _ _ _ (Functor.compConstIso ℕᵒᵖ F).hom)) =
        (preservesLimitNatIso F (J := ℕᵒᵖ)).hom := by
  let aa := (constLimAdj : (Functor.const ℕᵒᵖ : C ⥤ _) ⊣ lim)
  let bb := (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim)
  apply NatTrans.ext
  funext M
  apply limit.hom_ext
  intro n
  have h := congrArg (fun z ↦ z.app n)
    (mateEquiv_counit aa bb (TwoSquare.mk _ _ _ _
      (Functor.compConstIso ℕᵒᵖ F).hom) M)
  change (mateEquiv aa bb (TwoSquare.mk _ _ _ _
    (Functor.compConstIso ℕᵒᵖ F).hom)).app M ≫ limit.π _ n = _ at h
  change _ = 𝟙 _ ≫ F.map (limit.π M n) at h
  rw [Category.id_comp] at h
  exact h.trans (preservesLimitIso_hom_π F M n).symm

private theorem cbcRealizationLimit_mate_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasLimits C] [HasLimits D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
    [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive] [(lim : (ℕᵒᵖ ⥤ D) ⥤ D).Additive]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hphi : ∀ N : ℕ → C, IsIso (piComparison F N))
    (uA : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor)
    (uB : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor)
    (hA : ∀ X, uA.app X = exchangeDerivedUnit (lim : (ℕᵒᵖ ⥤ C) ⥤ C) X)
    (hB : ∀ X, uB.app X = exchangeDerivedUnit (lim : (ℕᵒᵖ ⥤ D) ⥤ D) X)
    (lambda : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      cbcTowerDerived F ⋙ (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor)
    (hnorm : CbcLimitNormalized F
      (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor
      (lim : (ℕᵒᵖ ⥤ D) ⥤ D).rightDerivedFunctor
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uA)
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uB) lambda) :
    lambda.hom =
      mateEquiv
        (constLimAdj : (Functor.const ℕᵒᵖ : C ⥤ _) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction
        (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction
        (Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ) ≪≫
          Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F) ≪≫
          (Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ)
            ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)).symm).hom := by
  have : PreservesLimitsOfShape (Discrete ℕ) F := natProducts F hphi
  have : PreservesLimitsOfShape ℕᵒᵖ F := natProducts_preservesTowers F
  let aa := (constLimAdj : (Functor.const ℕᵒᵖ : C ⥤ _) ⊣ lim)
  let bb := (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim)
  let tau := preservesLimitNatIso F (J := ℕᵒᵖ)
  have hm := cbcRealizationOrdinaryLimitMate F
  have he := cbcRealizationLimit_cochain_normalized F uA uB hA hB lambda hnorm
  have hh := exactDerivedMate_eq aa bb (Functor.compConstIso ℕᵒᵖ F) tau hm lambda he
  simpa only [exactDerivedMate, Functor.mapDerivedCategorySquareIso] using hh

/-- The specified mate is invertible for an exact product-preserving functor.
Source: Stacks 09BP and the normalized strict-limit lemma
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: apply lem-cbc-exact-product-functor-strict-limit. Its signed Roos formula
is induced by the canonical product map. On a K-injective tower it is the ordinary
limit comparison followed by a target resolution; adjunction transposition shows
that this is exactly cbcRealizationLimitMap. The normalized comparison is invertible,
and its augmentation equation also identifies the constant-diagram mate. -/
theorem cbcRealizationLimitMap_isIso {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (_products : ∀ M : ℕ → reductionModules T R, IsIso (piComparison F M)) :
    IsIso (cbcRealizationLimitMap F) := by
  have := ambient_exact T R
  have := ambient_exact S R'
  let a := Classical.choose (CategoryTheory.NormalizedLimitSquare.cornerData
    (ProEt.topology T) (reductionModuleRing T R) (completedRlim T R) (cbcRealizationRoosUnit T R)
      (cbcRealizationRoosUnit_derived T R))
  let b := Classical.choose (CategoryTheory.NormalizedLimitSquare.cornerData
    (ProEt.topology S) (reductionModuleRing S R') (completedRlim S R') (cbcRealizationRoosUnit S R')
      (cbcRealizationRoosUnit_derived S R'))
  let c := Classical.choose (CategoryTheory.NormalizedLimitSquare.comparisonData a b F _products)
  have hnorm := CategoryTheory.comparison_normalized F a b c
  have hm := cbcRealizationLimit_mate_eq F _products
    (cbcRealizationCochainUnit T R) (cbcRealizationCochainUnit S R')
    (cbcRealizationCochainUnit_eq T R) (cbcRealizationCochainUnit_eq S R') c.lambda hnorm
  change c.lambda.hom = cbcRealizationLimitMap F at hm
  rw [← hm]
  infer_instance

end LimitMateNormalization

attribute [local irreducible] limit

/-- Restriction of the scalar action on the ordinary module category.
Source: Stacks 03D3 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationRes (T : Scheme.{t}) :=
  proEtaleRingRestrictScalars (exchangeScalar d T)

/-- The recorded open extension adjunction transported by the section-normalized map.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationOpenAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcOpenShriek d j inferInstance ⊣
      proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
        (d.integralRingIso j) :=
  Adjunction.ofNatIsoRight (cbcOpenAdjunction d j inferInstance)
    (@asIso _ _ _ _ (cbcPullToRestriction d j) (cbcPullToRestriction_isIso d j)).symm

/-- Termwise completed open extension on strict towers, retaining every transition.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationTowerJ {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (cbcOpenShriek d j inferInstance)

/-- The exact derived open functor on completed strict towers.
Source: Stacks 03DJ (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationJ {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (cbcRealizationTowerJ d j).mapDerivedCategory

/-- Derived adjunction on completed towers with the normalized open unit.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationTowerAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcRealizationJ d j ⊣ d.towerPull j :=
  Adjunction.ofNatIsoRight
    ((cbcRealizationOpenAdj d j).whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    (d.towerModulePull j).rightDerivedFunctorIsoMapDerivedCategory

/-- The inverse tensor/open comparison is the transpose of the reduced open unit.
It is one strict-tower map, not a family of maps in separate derived categories.
Source: Stacks 03DI, 0E8I
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationReductionInv {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (cbcRealizationJ d j).obj ((completedReductionTower U d).obj K) ⟶
      (completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K) :=
  ((cbcRealizationTowerAdj d j).homEquiv _ _).symm
    ((completedReductionTower U d).map ((cbcDerivedOpenAdjunction d j).unit.app K) ≫
      (d.reductionTowerPullbackIso j).inv.app
        ((cbcDerivedOpenShriek d j inferInstance).obj K))

private theorem cbcTranspose_leftAdjointUniq
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R)
    {J J' : E ⥤ H} {S : H ⥤ E} (b : J ⊣ S) (b' : J' ⊣ S)
    (U : C ⥤ E) (V : D ⥤ H) (e : V ⋙ S ≅ R ⋙ U) (K : C) :
    (b.leftAdjointUniq b').hom.app (U.obj K) ≫
        (b'.homEquiv _ _).symm (U.map (a'.unit.app K) ≫ e.inv.app (L'.obj K)) =
      (b.homEquiv _ _).symm (U.map (a.unit.app K) ≫ e.inv.app (L.obj K)) ≫
        V.map ((a.leftAdjointUniq a').hom.app K) := by
  apply (b.homEquiv _ _).injective
  have hleft : ∀ f : J'.obj (U.obj K) ⟶ V.obj (L'.obj K),
      b.homEquiv _ _ ((b.leftAdjointUniq b').hom.app (U.obj K) ≫ f) =
        b'.homEquiv _ _ f := by
    intro f
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      Adjunction.unit_leftAdjointUniq_hom_app]
  rw [hleft]
  simp only [Functor.id_obj, Equiv.apply_symm_apply]
  conv_rhs => rw [b.homEquiv_naturality_right]
  simp only [Equiv.apply_symm_apply]
  have hn := e.inv.naturality ((a.leftAdjointUniq a').hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← U.map_comp,
    Adjunction.unit_leftAdjointUniq_hom_app]

/-- The tensor/open transpose is natural and invertible.
Source: Stacks 03DI, 0E8I
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: naturality is naturality of the open unit and of the strict reduction/pullback
comparison. On K-flat representatives its evaluation is the sheafified balancing map
j_!(Q) tensor P_n to j_!(Q tensor j^*P_n). Extension preserves K-flatness: tensor
with an acyclic ambient complex is extension of tensor with its exact restriction.
The inverse balancing maps commute with differentials and all quotient transitions.
Thus the inverse exists in the derived category of strict towers itself. -/
theorem cbcRealizationReductionInv_properties {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (∀ K : d.derived U, IsIso (cbcRealizationReductionInv d j K)) ∧
      ∀ (K L : d.derived U) (k : K ⟶ L),
        (cbcRealizationJ d j).map ((completedReductionTower U d).map k) ≫
            cbcRealizationReductionInv d j L =
          cbcRealizationReductionInv d j K ≫
            (completedReductionTower T d).map
              ((cbcDerivedOpenShriek d j inferInstance).map k) := by
  let a := cbcDerivedOpenAdjunction d j
  let a' := cbcEndpointDerivedOpenAdj d j
  let b := cbcRealizationTowerAdj d j
  let b' := cbcEndpointTowerOpenAdj d j
  have h := cbcTranspose_leftAdjointUniq a a' b b'
    (completedReductionTower U d) (completedReductionTower T d)
    (d.reductionTowerPullbackIso j)
  constructor
  · intro K
    have hh := h K
    change (b.leftAdjointUniq b').hom.app ((completedReductionTower U d).obj K) ≫
        cbcEndpointReductionInv d j K =
      cbcRealizationReductionInv d j K ≫
        (completedReductionTower T d).map ((a.leftAdjointUniq a').hom.app K) at hh
    have : IsIso (cbcEndpointReductionInv d j K) :=
      (cbcEndpointReductionInv_properties d j).1 K
    have : IsIso (cbcRealizationReductionInv d j K ≫
        (completedReductionTower T d).map ((a.leftAdjointUniq a').hom.app K)) := by
      rw [← hh]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((completedReductionTower T d).map
      ((a.leftAdjointUniq a').hom.app K))
  · intro K L k
    apply ((cbcRealizationTowerAdj d j).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [cbcRealizationReductionInv, Equiv.apply_symm_apply]
    have hu := (cbcDerivedOpenAdjunction d j).unit.naturality k
    dsimp only [Functor.comp_map, Functor.id_map] at hu
    have he := (d.reductionTowerPullbackIso j).inv.naturality
      ((cbcDerivedOpenShriek d j inferInstance).map k)
    dsimp only [Functor.comp_map] at he
    rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc, he]
    simp only [Category.assoc]

/-- The canonical tensor comparison on the full strict quotient tower.
Source: Stacks 0E8I (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationReduction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K) ≅
      (cbcRealizationJ d j).obj ((completedReductionTower U d).obj K) :=
  (@asIso _ _ _ _ (cbcRealizationReductionInv d j K)
    ((cbcRealizationReductionInv_properties d j).1 K)).symm

/-- Scalar restriction/open extension comparison, defined by the pullback mate.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationScalarOpenInv {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcRealizationRes d U ⋙ ProEtale.StrictTower.moduleJ A j ⟶
      cbcOpenShriek d j inferInstance ⋙ cbcRealizationRes d T :=
  (mateEquiv (cbcRealizationOpenAdj d j) (ProEtale.StrictTower.moduleJAdj A j)).symm
    (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv j
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d T) (exchangeScalar d U)
      (exchangeConstantIso j A) (d.integralRingIso j) (exchangeScalar_comm d j))
      (proEtaleRingRestrictionPullbackInv_isIso j
        (exchangeConstantRing T A) (d.completedRing T)
        (exchangeConstantRing U A) (d.completedRing U)
        (exchangeScalar d T) (exchangeScalar d U)
        (exchangeConstantIso j A) (d.integralRingIso j) (exchangeScalar_comm d j))).inv

section ScalarOpenInvertibility

attribute [local irreducible] cbcRealizationOpenAdj

/-- The scalar/open mate is invertible and preserves the normalized open adjunction.
Source: Stacks 03DI
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: the extension presheaf has the same direct-sum summands and restriction maps
after scalar restriction. Its action is the completed action composed with the scalar
map. Sheafification therefore gives the identity on the underlying additive sheaf.
The open unit includes the structure-map summand and the counit evaluates that
summand; both are unchanged. Its transpose is the displayed mate, so it is invertible. -/
theorem cbcRealizationScalarOpenInv_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (cbcRealizationScalarOpenInv d j) := by
  let R := exchangeConstantRing T A
  let S := d.completedRing T
  let adjS := Adjunction.ofIsRightAdjoint
    (proEtaleRingModulePullback j S (d.completedRing U) (d.integralRingIso j))
  let adjR := ProEtale.StrictTower.moduleJAdj A j
  let e := (cbcRealizationOpenAdj d j).leftAdjointUniq adjS
  obtain ⟨eS, ⟨hS⟩⟩ := proEtaleOpen_slicePresentation j
    S (d.completedRing U) (d.integralRingIso j)
  obtain ⟨eR, ⟨hR⟩⟩ := proEtaleOpen_slicePresentation j
    R (exchangeConstantRing U A) (exchangeConstantIso j A)
  let := SheafOfModules.localizedUnit_isIso j S
  let := SheafOfModules.localizedUnit_isIso j R
  let ffS := (SheafOfModules.localizedModuleAdjunctionIndependent
    S (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit
  let ffR := (SheafOfModules.localizedModuleAdjunctionIndependent
    R (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit
  have := ffS.full
  have := ffS.faithful
  have := ffR.full
  have := ffR.faithful
  have : (cbcOpenShriek d j inferInstance).Full := Functor.Full.of_iso (e ≪≫ hS).symm
  have : (cbcOpenShriek d j inferInstance).Faithful :=
    Functor.Faithful.of_iso (e ≪≫ hS).symm
  have : (moduleJ A j).Full := Functor.Full.of_iso hR.symm
  have : (moduleJ A j).Faithful := Functor.Faithful.of_iso hR.symm
  have : IsIso (cbcRealizationOpenAdj d j).unit := inferInstance
  obtain ⟨_, _, scalarIso, _, _⟩ :=
    SheafOfModules.RingedOpenScalar.comparison.{t + 1, t, 0, t + 2}
      (ProEt.mk j) (exchangeScalar d T)
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  let LR := SheafOfModules.localizedModuleExtension.{t} R (ProEt.mk j)
  have hs : LR.essImage
      ((cbcRealizationRes d T).obj ((cbcOpenShriek d j inferInstance).obj M)) := by
    exact ⟨(SheafOfModules.RingedOpenScalar.sliceScalars.{t + 1, t, 0}
      (ProEt.mk j) (exchangeScalar d T)).obj (eS.functor.obj M),
      ⟨(scalarIso.app (eS.functor.obj M)).symm ≪≫
        (cbcRealizationRes d T).mapIso ((e ≪≫ hS).app M).symm⟩⟩
  have ht : (eR.functor ⋙ LR).essImage
      ((cbcRealizationRes d T).obj ((cbcOpenShriek d j inferInstance).obj M)) :=
    Functor.essImage_comp_apply_of_essSurj.mpr hs
  have : IsIso (adjR.counit.app
      ((cbcRealizationRes d T).obj ((cbcOpenShriek d j inferInstance).obj M))) :=
    adjR.isIso_counit_app_iff_mem_essImage.mpr (Functor.essImage.ofNatIso hR.symm ht)
  change IsIso (((mateEquiv (cbcRealizationOpenAdj d j) adjR).symm _).app M)
  simp only [mateEquiv_symm_apply, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_map, Functor.comp_obj, Category.id_comp]
  have : IsIso ((proEtaleRingRestrictionPullbackInv j
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d T) (exchangeScalar d U)
      (exchangeConstantIso j A) (d.integralRingIso j) (exchangeScalar_comm d j))) :=
    proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _
  infer_instance

end ScalarOpenInvertibility

/-- Canonical scalar/open comparison on ordinary modules.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationScalarOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcOpenShriek d j inferInstance ⋙ cbcRealizationRes d T ≅
      cbcRealizationRes d U ⋙ ProEtale.StrictTower.moduleJ A j :=
  (@asIso _ _ _ _ (cbcRealizationScalarOpenInv d j)
    (cbcRealizationScalarOpenInv_isIso d j)).symm

/-- Apply scalar/open comparison to a whole strict diagram, then derive exactly.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationTowerScalarOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcRealizationJ d j ⋙ exchangeTowerRes d T ≅
      exchangeTowerRes d U ⋙ ProEtale.StrictTower.J A j :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.whiskeringRightObjCompIso _ _ ≪≫
        (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (cbcRealizationScalarOpen d j) ≪≫
        (Functor.whiskeringRightObjCompIso _ _).symm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Scalar/open comparison on single derived objects, by exact descent.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationDerivedScalarOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcDerivedOpenShriek d j inferInstance ⋙ (cbcRealizationRes d T).mapDerivedCategory ≅
      (cbcRealizationRes d U).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (cbcRealizationScalarOpen d j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The quotient/open tensor identification followed by scalar/open identification.
Source: Stacks 03DI, 0E8I
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationQuotientOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (exchangeTowerRes d T).obj
        ((completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K)) ≅
      (ProEtale.StrictTower.J A j).obj
        ((exchangeTowerRes d U).obj ((completedReductionTower U d).obj K)) :=
  (exchangeTowerRes d T).mapIso (cbcRealizationReduction d j K) ≪≫
    (cbcRealizationTowerScalarOpen d j).app ((completedReductionTower U d).obj K)

-- Keep the forgetful comparison abstract before specializing the coefficient sheaves.
private theorem cbcRealizationRestrictionForgetsProducts
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{t + 1}} (a : R ⟶ S)
    [PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{t + 1} S)] :
    PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.restrictScalars.{t + 1} a ⋙ SheafOfModules.toSheaf.{t + 1} R) := by
  let e : SheafOfModules.restrictScalars.{t + 1} a ⋙ SheafOfModules.toSheaf.{t + 1} R ≅
      SheafOfModules.toSheaf.{t + 1} S :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) (fun f ↦ by rfl)
  exact preservesLimitsOfShape_of_natIso e.symm

-- The cached universe-polymorphic sheafification instance gets stuck on the coefficient universe.
attribute [-instance] SheafOfModules.RingedCoefficientProjection.cachedSheafifyModules in
/-- Products are preserved by scalar restriction and by quasi-compact constant open extension.
Source: Stacks 03D3, 09BP
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: restriction leaves the underlying additive sheaves and all limits unchanged.
For open extension, use j!N = ker(j*N to i*i^-1j*N). Direct images preserve
products sectionwise and closed inverse image preserves products on the pro-etale
site. Kernels commute with products. These are the canonical projection maps,
including for the empty product; no qcqs hypothesis on the ambient scheme is used. -/
theorem cbcRealizationProducts (T : Scheme.{t}) :
    (∀ M : ℕ → reductionModules T (d.completedRing T),
      IsIso (piComparison (cbcRealizationRes d T) M)) ∧
      ∀ {U : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
        (M : ℕ → ProEtale.StrictTower.Modules A U),
        IsIso (piComparison (ProEtale.StrictTower.moduleJ A j) M) := by
  constructor
  · intro M
    let R := reductionModuleRing T (exchangeConstantRing T A)
    let S := reductionModuleRing T (d.completedRing T)
    let G := SheafOfModules.toSheaf.{t + 1} R
    have : PreservesLimitsOfShape (Discrete (ULift.{t + 1} ℕ))
        (SheafOfModules.toSheaf.{t + 1} S) :=
      ((moduleSheaves_colimits_forgetful S).2.2.2.2.2 _).1
    have : PreservesLimitsOfShape (Discrete (ULift.{t + 1} ℕ)) G :=
      ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 _).1
    have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{t + 1} S) :=
      preservesLimitsOfShape_of_equiv
        (Discrete.equivalence (Equiv.ulift : ULift.{t + 1} ℕ ≃ ℕ)) _
    have : PreservesLimitsOfShape (Discrete ℕ) G :=
      preservesLimitsOfShape_of_equiv
        (Discrete.equivalence (Equiv.ulift : ULift.{t + 1} ℕ ≃ ℕ)) _
    have : ReflectsLimitsOfShape (Discrete ℕ) G :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    have : PreservesLimitsOfShape (Discrete ℕ) (cbcRealizationRes d T ⋙ G) :=
      cbcRealizationRestrictionForgetsProducts (R := R) (S := S)
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (exchangeScalar d T))
    have : PreservesLimitsOfShape (Discrete ℕ) (cbcRealizationRes d T) :=
      preservesLimitsOfShape_of_reflects_of_preserves _ G
    infer_instance
  · intro U j _ _ M
    let W := ProEt.mk j
    let R := exchangeConstantRing T A
    have : IsOpenImmersion W.hom := show IsOpenImmersion j from inferInstance
    have : QuasiCompact W.hom := show QuasiCompact j from inferInstance
    let L : SheafOfModules.{t + 1} ((proEtaleModuleCoefficients R).over W) ⥤
        SheafOfModules.{t + 1} (proEtaleModuleCoefficients R) :=
      proEtaleRingedExtensionByZero W R
    have : ∀ N : ULift.{t + 1} ℕ →
        ringedSiteModules.{t + 1} ((proEtaleModuleCoefficients R).over W),
        PreservesLimit (Discrete.functor N) L := fun N ↦ by
      have := (proEtaleRingedExtensionByZero_products W R (ULift.{t + 1} ℕ) N).1
      exact PreservesProduct.of_iso_comparison L N
    have : PreservesLimitsOfShape (Discrete (ULift.{t + 1} ℕ)) L :=
      preservesLimitsOfShape_of_discrete L
    have : PreservesLimitsOfShape (Discrete ℕ) L :=
      preservesLimitsOfShape_of_equiv
        (Discrete.equivalence (Equiv.ulift : ULift.{t + 1} ℕ ≃ ℕ)) L
    obtain ⟨e, ⟨h⟩⟩ := proEtaleOpen_slicePresentation j R (exchangeConstantRing U A)
      (exchangeConstantIso j A)
    have : PreservesLimitsOfShape (Discrete ℕ)
        (e.functor ⋙ SheafOfModules.localizedModuleExtension.{t} R (ProEt.mk j)) := by
      change PreservesLimitsOfShape (Discrete ℕ) (e.functor ⋙ L)
      infer_instance
    have : PreservesLimitsOfShape (Discrete ℕ) (ProEtale.StrictTower.moduleJ A j) :=
      preservesLimitsOfShape_of_natIso h.symm
    infer_instance

/-- The specified scalar-restriction/Rlim isomorphism.
Source: Stacks 03D3 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationResLimit (T : Scheme.{t}) :
    completedRlim T (d.completedRing T) ⋙ (cbcRealizationRes d T).mapDerivedCategory ≅
      exchangeTowerRes d T ⋙ completedRlim T (exchangeConstantRing T A) :=
  @asIso _ _ _ _ (cbcRealizationLimitMap (cbcRealizationRes d T))
    (cbcRealizationLimitMap_isIso _ (cbcRealizationProducts d T).1)

/-- The specified constant open-extension/Rlim isomorphism.
Source: Stacks 09BP (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationOpenLimit (d : AdicCoefficientDatum A) {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j] :
    completedRlim U (exchangeConstantRing U A) ⋙
        (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory ≅
      ProEtale.StrictTower.J A j ⋙ completedRlim T (exchangeConstantRing T A) :=
  @asIso _ _ _ _ (cbcRealizationLimitMap (ProEtale.StrictTower.moduleJ A j))
    (cbcRealizationLimitMap_isIso _ ((cbcRealizationProducts d T).2 j))

/-- Direct-image/Rlim comparison for constant coefficients, as the conjugate
of the identity constant-diagram/pullback comparison, including both units.
Source: Stacks 0A07 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationPushLimit {U T : Scheme.{t}} (f : U ⟶ T) :
    completedRlim U (exchangeConstantRing U A) ⋙
        (ProEtale.StrictTower.moduleDirectImage A f).rightDerivedFunctor ≅
      ProEtale.StrictTower.R A f ⋙ completedRlim T (exchangeConstantRing T A) :=
  conjugateIsoEquiv
    (((proEtaleRingModuleAdjunction f (exchangeConstantRing T A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).mapDerivedCategoryRightDerivedAdjunction
      ).comp (cbcRealizationLimitAdj U (exchangeConstantRing U A)))
    ((cbcRealizationLimitAdj T (exchangeConstantRing T A)).comp (ProEtale.StrictTower.adj A f))
    (cbcRealizationConst (ProEtale.StrictTower.modulePullback A f)).symm

/-- The single-object direct-image/scalar comparison, with its published universal units.
Source: Stacks 0D6E (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationResPush {U T : Scheme.{t}} (f : U ⟶ T) :
    d.push f ⋙ (cbcRealizationRes d T).mapDerivedCategory ≅
      (cbcRealizationRes d U).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleDirectImage A f).rightDerivedFunctor :=
  proEtaleRingRestrictionDerivedDirectImage f
    (exchangeConstantRing T A) (d.completedRing T)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d T) (exchangeScalar d U)
    (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f)

/-- Canonical constant-tower presentation of completed pullback.
Source: Stacks 099M and finite reduction comparison
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationPullLimit {U T : Scheme.{t}} (f : U ⟶ T) (K : d.derived T) :
    (cbcRealizationRes d U).mapDerivedCategory.obj ((d.completedPull f).obj K) ≅
      (completedRlim U (exchangeConstantRing U A)).obj
        ((ProEtale.StrictTower.G A f).obj
          ((exchangeTowerRes d T).obj ((completedReductionTower T d).obj K))) :=
  (cbcRealizationResLimit d U).app
      ((d.towerPull f).obj ((completedReductionTower T d).obj K)) ≪≫
    (completedRlim U (exchangeConstantRing U A)).mapIso
      ((exchangeResPull d f).app ((completedReductionTower T d).obj K))

variable {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- The actual strict-tower proper/open composite, defined before evaluation.
The proper mate is the normalization dependency's mate on constant A towers.
Source: blueprint Definition 1939 and strict normalization, final paragraph
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationStrict (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z) (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (M : ProEtale.StrictTower.Derived A X) :
    (ProEtale.StrictTower.G A g).obj
        ((ProEtale.StrictTower.R A c.g).obj ((ProEtale.StrictTower.J A c.i).obj M)) ⟶
      (ProEtale.StrictTower.R A c'.g).obj
        ((ProEtale.StrictTower.J A c'.i).obj ((ProEtale.StrictTower.G A g').obj M)) :=
  (exchangeConstantSquare (A := A) sp).exchangeTowerMate.app
      ((ProEtale.StrictTower.J A c.i).obj M) ≫
    (ProEtale.StrictTower.R A c'.g).map
      ((ProEtale.StrictTower.beta A g' c'.i c.i gbar sj.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom.app M)

/-- Source identification: specified strict projection, scalar/limit comparison,
proper corner b, and canonical quotient/open tensor comparison, in that order.
Source: blueprint strict realization, proof step 9
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationSource (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z) (K : d.derived X) :
    (cbcRealizationRes d Y').mapDerivedCategory.obj
        ((d.completedPull g).obj
          ((d.push c.g).obj ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K))) ≅
      (completedRlim Y' (exchangeConstantRing Y' A)).obj
        ((ProEtale.StrictTower.G A g).obj
          ((ProEtale.StrictTower.R A c.g).obj
            ((ProEtale.StrictTower.J A c.i).obj
              ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K))))) :=
  ((cbcRealizationRes d Y').mapDerivedCategory).mapIso
      ((completedRlim Y' (d.completedRing Y')).mapIso
        (d.towerH (f := c.g) (f' := c'.g) (g := g) (g' := gbar)
          ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K))) ≪≫
    (cbcRealizationResLimit d Y').app _ ≪≫
    (completedRlim Y' (exchangeConstantRing Y' A)).mapIso
      ((exchangeCornerB d c.g g).app _ ≪≫
        (ProEtale.StrictTower.G A g).mapIso
          ((ProEtale.StrictTower.R A c.g).mapIso (cbcRealizationQuotientOpen d c.i K)))

/-- Target identification: inverse direct-image/limit and extension/limit maps,
followed by inverse completed-pullback, scalar/open, and scalar/direct-image maps.
Source: blueprint strict realization, proof step 9
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationTarget (c' : Compactification f') (g' : X' ⟶ X)
    [qc : QuasiCompact c'.i] (K : d.derived X) :
    (completedRlim Y' (exchangeConstantRing Y' A)).obj
        ((ProEtale.StrictTower.R A c'.g).obj
          ((ProEtale.StrictTower.J A c'.i).obj ((ProEtale.StrictTower.G A g').obj
            ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K))))) ≅
      (cbcRealizationRes d Y').mapDerivedCategory.obj
        ((d.push c'.g).obj ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).obj
          ((d.completedPull g').obj K))) :=
  ((cbcRealizationPushLimit (A := A) c'.g).app _).symm ≪≫
    (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor.mapIso
      (((cbcRealizationOpenLimit d c'.i).app _).symm ≪≫
        (ProEtale.StrictTower.moduleJ A c'.i).mapDerivedCategory.mapIso
          (cbcRealizationPullLimit d g' K).symm ≪≫
        ((cbcRealizationDerivedScalarOpen d c'.i).app ((d.completedPull g').obj K)).symm) ≪≫
    ((cbcRealizationResPush d c'.g).app _).symm

section Evaluation
open AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open AlgebraicGeometry.ProEtale.RelativeCompactSupport
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] proEtaleRingModuleAdjunctionNormalized
  proEtaleRingModuleUnitSection proEtaleRingCompositeCoefficients
  proEtaleRingDerivedPullbackFactors CochainComplex.IsAcyclicTensorKFlat
  SheafOfModules.IsFlatOnSite proEtaleRingDirectImageMap

variable (B : Type (t + 1)) [CommRing B]
end Evaluation

attribute [local irreducible] cbcRealizationResLimit cbcRealizationPushLimit
  cbcRealizationOpenLimit cbcRealizationDerivedScalarOpen cbcRealizationSource
  cbcRealizationTarget

/-- The published completed open factor, with its derived quasi-compactness instance.
Source: blueprint Definition 1939
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationOpenFactor [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  (cbcDatumCompletedExchange d sj r a ha).app K

end AlgebraicGeometry.Scheme
