/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.LocallyClosedModuleExtensionData
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import WeilConjectures.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
import WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
import WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction
import WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedExactMate
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.RingTheory.FactorsThroughLocalization
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrows
import WeilConjectures.SecSmoothPurity.CochainInverseComparison
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-! Normalized locally closed module extension: assembly from the fixed model. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Witnesses for the exact module extensions in the assertion. The open adjunction and
closed counit normalize restriction. The coefficients of every arrow are inverse images.
Source: Stacks, Tags 09AA, 09BM, 09BN, 03DI and 03DJ
(auxiliary; not a blueprint node). -/
structure LocallyClosedExtensionData where
  extension : ∀ {S X : LocallyClosedCoefficients.{u}}, LocallyClosedCoefficientImmersion S X →
    proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring
  additive : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (extension a).Additive
  finiteLimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteLimits (extension a)
  finiteColimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteColimits (extension a)
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), extension a ⋙ a.pull ≅ 𝟭 _
  openAdjunction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsOpenImmersion a.hom),
    extension a ⊣ a.pull
  openNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsOpenImmersion a.hom),
    LocallyClosedOpenNormalization (extension a) a.pull (restriction a) (openAdjunction a ha)
  closedComparison : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsClosedImmersion a.hom),
    extension a ≅ a.push
  closedNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsClosedImmersion a.hom),
    LocallyClosedClosedNormalization (extension a) a.push a.pull (restriction a)
      (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).counit
      (closedComparison a ha)
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    extension b ⋙ extension a ≅ extension (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u},
    extension (.identity X) ≅ 𝟭 (proEtaleRingModules X.scheme X.ring)

attribute [instance] LocallyClosedExtensionData.additive LocallyClosedExtensionData.finiteLimits
  LocallyClosedExtensionData.finiteColimits

namespace LocallyClosedExtensionData

/-- The actual termwise extension on the ordinary unbounded derived categories.
Source: Stacks, Tags 015F and 05RU
(auxiliary; not a blueprint node). -/
abbrev derived (E : LocallyClosedExtensionData.{u}) {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) := (E.extension a).mapDerivedCategory

/-- The same comparisons on unbounded derived categories, required to be the
localizations of the module comparisons on every cochain complex, not arbitrary isos.
Source: Stacks, Tags 05RU and 015F; exact-functor localization
(auxiliary; not a blueprint node). -/
structure DerivedCoherence (E : LocallyClosedExtensionData.{u}) where
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), E.derived a ⋙ a.pull.mapDerivedCategory ≅ 𝟭 _
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    E.derived b ⋙ E.derived a ≅ E.derived (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u}, E.derived (.identity X) ≅ 𝟭 _
  restrictionTermwise : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X)
    (K : CochainComplex (proEtaleRingModules S.scheme S.ring) ℤ),
    (restriction a).hom.app (DerivedCategory.Q.obj K) =
      a.pull.mapDerivedCategory.map ((E.extension a).mapDerivedCategoryFactors.hom.app K) ≫
        a.pull.mapDerivedCategoryFactors.hom.app
          (((E.extension a).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (E.restriction a) (.up ℤ)).hom.app K)
  gammaTermwise : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (K : CochainComplex (proEtaleRingModules T.scheme T.ring) ℤ),
    (gamma a b).hom.app (DerivedCategory.Q.obj K) ≫
        (E.extension (a.comp b)).mapDerivedCategoryFactors.hom.app K =
      (E.derived a).map ((E.extension b).mapDerivedCategoryFactors.hom.app K) ≫
        (E.extension a).mapDerivedCategoryFactors.hom.app
          (((E.extension b).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (E.gamma a b) (.up ℤ)).hom.app K)
  identityTermwise : ∀ (X : LocallyClosedCoefficients.{u})
    (K : CochainComplex (proEtaleRingModules X.scheme X.ring) ℤ),
    (identity X).hom.app (DerivedCategory.Q.obj K) =
      (E.extension (.identity X)).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (E.identity X) (.up ℤ)).hom.app K)
  full : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (E.derived a).Full
  faithful : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), (E.derived a).Faithful
  homBijection : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X)
    (M N : DerivedCategory (proEtaleRingModules S.scheme S.ring)),
    Function.Bijective (fun f : (E.derived a).obj M ⟶ (E.derived a).obj N ↦
      (restriction a).inv.app M ≫ a.pull.mapDerivedCategory.map f ≫ (restriction a).hom.app N)
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      gamma a (.identity S) ≪≫ eqToIso (congrArg E.derived h) =
        Functor.isoWhiskerRight (identity S) (E.derived a) ≪≫ Functor.leftUnitor (E.derived a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      gamma (.identity X) a ≪≫ eqToIso (congrArg E.derived h) =
        Functor.isoWhiskerLeft (E.derived a) (identity X) ≪≫ Functor.rightUnitor (E.derived a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (gamma b d) (E.derived a) ≪≫ gamma a (b.comp d) =
        Functor.associator (E.derived d) (E.derived b) (E.derived a) ≪≫
          Functor.isoWhiskerLeft (E.derived d) (gamma a b) ≪≫ gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.derived h)

end LocallyClosedExtensionData

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage

private structure OpenNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) where
  adj : F ⊣ L
  normalized : LocallyClosedOpenNormalization F L r adj

private theorem openNormalization_nonempty
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C)
    (h : ∃ adj : F ⊣ L, LocallyClosedOpenNormalization F L r adj) :
    Nonempty (OpenNormalization F L r) := ⟨⟨h.choose, h.choose_spec⟩⟩

@[irreducible] private def openNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C)
    (h : ∃ adj : F ⊣ L, LocallyClosedOpenNormalization F L r adj) :
    OpenNormalization F L r := Classical.choice (openNormalization_nonempty F L r h)

private structure ClosedNormalization
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C) where
  iso : F ≅ P
  normalized : LocallyClosedClosedNormalization F P L r d iso

private theorem closedNormalization_nonempty
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C)
    (h : ∃ e : F ≅ P, LocallyClosedClosedNormalization F P L r d e) :
    Nonempty (ClosedNormalization F P L r d) := ⟨⟨h.choose, h.choose_spec⟩⟩

@[irreducible] private def closedNormalization
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C)
    (h : ∃ e : F ≅ P, LocallyClosedClosedNormalization F P L r d e) :
    ClosedNormalization F P L r d :=
  Classical.choice (closedNormalization_nonempty F P L r d h)

end AlgebraicGeometry.Scheme
