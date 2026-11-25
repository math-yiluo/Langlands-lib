/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenHorizontalComposition

/-!
# Unbounded proper/open composition

Source: Stacks Project, Tags 0F7C and 0F7D.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private lemma comp_fac
    {C D E : Type v} [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) :
    Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorCompIso' F G e).hom =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh ≫
      H.rightDerivedFunctorUnit := by
  have hc : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [← hc, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc]
  exact Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso C (.up ℤ)) _

set_option backward.isDefEq.respectTransparency false in
private lemma comp_unit_app
    {C D E : Type v} [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (T : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app T =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T) := by
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) T
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, hi]
  erw [DerivedCategory.Qh.map_id]
  simp only [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]

-- Comparing iterated sheaf functors requires unfolding the derived-category interfaces.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in

private lemma derived_comp_eq (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) g f).hom =
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar (ModuleCat.{u + 1} Λ) g) (lowerStar (ModuleCat.{u + 1} Λ) f)
        (lowerStarComp (ModuleCat.{u + 1} Λ) g f)).hom := by
  rw [Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (g ≫ f))
    _ (upperStarComp (ModuleCat.{u + 1} Λ) g f) (by
      exact (congrArg Iso.hom
        (conjugateIsoEquiv_upperStarComp (ModuleCat.{u + 1} Λ) g f)).symm)]
  simp only [rightDerivedLowerStarComp, Iso.symm_hom, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv]
  rfl

private theorem geometric_comp_fac
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.rightDerivedFunctorCompUnit (f)_*[ModuleCat.{u + 1} Λ]
        (g)_*[ModuleCat.{u + 1} Λ] ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) f g).hom =
    Functor.whiskerRight
        (NatTrans.mapHomotopyCategory
          (lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom (.up ℤ)) DerivedCategory.Qh ≫
      ((f ≫ g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorUnit := by
  rw [derived_comp_eq Λ g f]
  exact comp_fac _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem generic_vertical_pasting
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type v}
    [Category.{w} A₀] [Category.{w} A₁] [Category.{w} A₂]
    [Category.{w} B₀] [Category.{w} B₁] [Category.{w} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
    [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
    [Abelian.HasKInjectiveResolutions A₀] [Abelian.HasKInjectiveResolutions A₁]
    [Abelian.HasKInjectiveResolutions B₀] [Abelian.HasKInjectiveResolutions B₁]
    (G₁ : A₀ ⥤ A₁) (G₂ : A₁ ⥤ A₂) (G : A₀ ⥤ A₂)
    (H₁ : B₀ ⥤ B₁) (H₂ : B₁ ⥤ B₂) (H : B₀ ⥤ B₂)
    (E₀ : A₀ ⥤ B₀) (E₁ : A₁ ⥤ B₁) (E₂ : A₂ ⥤ B₂)
    [G₁.Additive] [G₂.Additive] [G.Additive]
    [H₁.Additive] [H₂.Additive] [H.Additive]
    [E₀.Additive] [E₁.Additive] [E₂.Additive]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]
    [G₁.PreservesKInjectiveComplexes] [H₁.PreservesKInjectiveComplexes]
    (g : G₁ ⋙ G₂ ≅ G) (h : H₁ ⋙ H₂ ≅ H)
    (e₁ : G₁ ⋙ E₁ ⟶ E₀ ⋙ H₁) (e₂ : G₂ ⋙ E₂ ⟶ E₁ ⋙ H₂)
    (e : G ⋙ E₂ ⟶ E₀ ⋙ H)
    (he : ∀ X, E₂.map (g.hom.app X) ≫ e.app X =
      e₂.app (G₁.obj X) ≫ H₂.map (e₁.app X) ≫ h.hom.app (E₀.obj X))
    (c₁ : G₁.rightDerivedFunctor ⋙ E₁.mapDerivedCategory ⟶
      E₀.mapDerivedCategory ⋙ H₁.rightDerivedFunctor)
    (c₂ : G₂.rightDerivedFunctor ⋙ E₂.mapDerivedCategory ⟶
      E₁.mapDerivedCategory ⋙ H₂.rightDerivedFunctor)
    (c : G.rightDerivedFunctor ⋙ E₂.mapDerivedCategory ⟶
      E₀.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hc₁ : ∀ J : HomotopyCategory A₀ (.up ℤ),
      E₁.mapDerivedCategory.map (G₁.rightDerivedFunctorUnit.app J) ≫
          c₁.app (DerivedCategory.Qh.obj J) =
        E₁.mapDerivedCategoryFactorsh.hom.app
          ((G₁.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₁ (.up ℤ)).app J) ≫
        H₁.rightDerivedFunctorUnit.app ((E₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
        H₁.rightDerivedFunctor.map (E₀.mapDerivedCategoryFactorsh.inv.app J))
    (hc₂ : ∀ J : HomotopyCategory A₁ (.up ℤ),
      E₂.mapDerivedCategory.map (G₂.rightDerivedFunctorUnit.app J) ≫
          c₂.app (DerivedCategory.Qh.obj J) =
        E₂.mapDerivedCategoryFactorsh.hom.app
          ((G₂.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₂ (.up ℤ)).app J) ≫
        H₂.rightDerivedFunctorUnit.app ((E₁.mapHomotopyCategory (.up ℤ)).obj J) ≫
        H₂.rightDerivedFunctor.map (E₁.mapDerivedCategoryFactorsh.inv.app J))
    (hc : ∀ J : HomotopyCategory A₀ (.up ℤ),
      E₂.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app J) ≫
          c.app (DerivedCategory.Qh.obj J) =
        E₂.mapDerivedCategoryFactorsh.hom.app
          ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e (.up ℤ)).app J) ≫
        H.rightDerivedFunctorUnit.app ((E₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
        H.rightDerivedFunctor.map (E₀.mapDerivedCategoryFactorsh.inv.app J))
    (cG : G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor ≅ G.rightDerivedFunctor)
    (cH : H₁.rightDerivedFunctor ⋙ H₂.rightDerivedFunctor ≅ H.rightDerivedFunctor)
    (hcG : Functor.rightDerivedFunctorCompUnit G₁ G₂ ≫
        Functor.whiskerLeft DerivedCategory.Qh cG.hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory g.hom (.up ℤ))
        DerivedCategory.Qh ≫ G.rightDerivedFunctorUnit)
    (hcH : Functor.rightDerivedFunctorCompUnit H₁ H₂ ≫
        Functor.whiskerLeft DerivedCategory.Qh cH.hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory h.hom (.up ℤ))
        DerivedCategory.Qh ≫ H.rightDerivedFunctorUnit)
    (K : DerivedCategory A₀) :
    c.app K =
      E₂.mapDerivedCategory.map
        (cG.inv.app K) ≫
      c₂.app (G₁.rightDerivedFunctor.obj K) ≫
      H₂.rightDerivedFunctor.map (c₁.app K) ≫
      cH.hom.app
        (E₀.mapDerivedCategory.obj K) := by
  let a : (G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor) ⋙
      E₂.mapDerivedCategory ⟶ E₀.mapDerivedCategory ⋙ H.rightDerivedFunctor :=
    Functor.whiskerRight cG.hom E₂.mapDerivedCategory ≫
      c
  let b : (G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor) ⋙
      E₂.mapDerivedCategory ⟶ E₀.mapDerivedCategory ⋙ H.rightDerivedFunctor :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft G₁.rightDerivedFunctor
        (c₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (c₁)
        H₂.rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft E₀.mapDerivedCategory cH.hom
  have hi (X : HomotopyCategory.KInjectives A₀) :
      IsIso ((Functor.rightDerivedFunctorCompUnit G₁ G₂).app
        ((HomotopyCategory.KInjectives.ι (C := A₀)).obj X)) := by
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    have h₁ : IsIso (G₁.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A₀ (.up ℤ)).obj J)) := inferInstance
    have h₂ : IsIso (G₂.rightDerivedFunctorUnit.app
      ((G₁.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A₀ (.up ℤ)).obj J))) := by
      change IsIso (G₂.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient A₁ (.up ℤ)).obj
          ((G₁.mapHomologicalComplex (.up ℤ)).obj J)))
      infer_instance
    let h₁ := h₁
    let h₂ := h₂
    change IsIso ((Functor.rightDerivedFunctorCompUnit G₁ G₂).app
      ((HomotopyCategory.quotient A₀ (.up ℤ)).obj J))
    rw [comp_unit_app G₁ G₂]
    exact (asIso (G₂.rightDerivedFunctorUnit.app _ ) ≪≫
      G₂.rightDerivedFunctor.mapIso (asIso (G₁.rightDerivedFunctorUnit.app _))).isIso_hom
  have : ((G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor) ⋙
      E₂.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight (Functor.rightDerivedFunctorCompUnit G₁ G₂)
        E₂.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A₀ (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (((G₁ ⋙ G₂).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        E₂.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _ (fun X ↦ ?_)
    let _ := hi X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
    change IsIso (E₂.mapDerivedCategory.map
      ((Functor.rightDerivedFunctorCompUnit G₁ G₂).app
        ((HomotopyCategory.KInjectives.ι (C := A₀)).obj X)) ≫ 𝟙 _)
    infer_instance
  have hab : a = b := by
    apply Functor.rightDerived_ext
      ((G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor) ⋙ E₂.mapDerivedCategory)
      (Functor.whiskerRight (Functor.rightDerivedFunctorCompUnit G₁ G₂)
        E₂.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A₀ (.up ℤ))
    apply NatTrans.ext
    funext J
    simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, Category.assoc]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp,
      Category.id_comp]
    have hcG := congr_app hcG J
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at hcG
    erw [← E₂.mapDerivedCategory.map_comp_assoc, hcG,
      E₂.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    erw [hc J]
    have hn₂ := (c₂).naturality
      (G₁.rightDerivedFunctorUnit.app J)
    simp only [Functor.comp_map] at hn₂
    erw [comp_unit_app G₁ G₂ J, E₂.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    erw [reassoc_of% hn₂]
    erw [reassoc_of% hc₂ ((G₁.mapHomotopyCategory (.up ℤ)).obj J)]
    have h₁ := hc₁ J
    have h₁' : E₁.mapDerivedCategoryFactorsh.inv.app
        ((G₁.mapHomotopyCategory (.up ℤ)).obj J) ≫
        E₁.mapDerivedCategory.map (G₁.rightDerivedFunctorUnit.app J) ≫
        (c₁).app
          (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₁ (.up ℤ)).app J) ≫
        H₁.rightDerivedFunctorUnit.app ((E₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
        H₁.rightDerivedFunctor.map (E₀.mapDerivedCategoryFactorsh.inv.app J) := by
      apply (cancel_epi (E₁.mapDerivedCategoryFactorsh.hom.app
        ((G₁.mapHomotopyCategory (.up ℤ)).obj J))).1
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      simpa only [Functor.comp_obj, Category.assoc] using h₁
    erw [← H₂.rightDerivedFunctor.map_comp_assoc,
      ← H₂.rightDerivedFunctor.map_comp_assoc]
    simp only [Category.assoc]
    erw [h₁']
    erw [H₂.rightDerivedFunctor.map_comp, H₂.rightDerivedFunctor.map_comp]
    simp only [Category.assoc]
    have hn := H₂.rightDerivedFunctorUnit.naturality
      ((NatTrans.mapHomotopyCategory e₁ (.up ℤ)).app J)
    simp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    have hnH := cH.hom.naturality (E₀.mapDerivedCategoryFactorsh.inv.app J)
    simp only [Functor.comp_map] at hnH
    erw [hnH]
    have hcH := congr_app hcH
      ((E₀.mapHomotopyCategory (.up ℤ)).obj J)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, comp_unit_app] at hcH
    erw [Category.assoc] at hcH
    erw [reassoc_of% hcH]
    have hnE := E₂.mapDerivedCategoryFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategory g.hom (.up ℤ)).app J)
    simp only [Functor.comp_map] at hnE
    simp only [Functor.comp_obj] at hnE
    erw [reassoc_of% hnE]
    have ht : Functor.whiskerRight g.hom E₂ ≫ e =
        Functor.whiskerLeft G₁ e₂ ≫ Functor.whiskerRight e₁ H₂ ≫
          Functor.whiskerLeft E₀ h.hom := by
      ext X
      exact he X
    have hh := congr_app
      (congrArg (fun t => NatTrans.mapHomotopyCategory t (.up ℤ)) ht) J
    simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at hh
    change (E₂.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory g.hom (.up ℤ)).app J) ≫
          (NatTrans.mapHomotopyCategory e (.up ℤ)).app J =
      (NatTrans.mapHomotopyCategory e₂ (.up ℤ)).app
          ((G₁.mapHomotopyCategory (.up ℤ)).obj J) ≫
        (H₂.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory e₁ (.up ℤ)).app J) ≫
        (NatTrans.mapHomotopyCategory h.hom (.up ℤ)).app
          ((E₀.mapHomotopyCategory (.up ℤ)).obj J) at hh
    erw [← DerivedCategory.Qh.map_comp_assoc, hh]
    simp only [DerivedCategory.Qh.map_comp, Category.assoc]
    rfl
  apply (Iso.eq_inv_comp (E₂.mapDerivedCategory.mapIso (cG.app K))).2
  simpa only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.assoc,
    Category.id_comp, CategoryTheory.Functor.mapIso_hom, Iso.app_hom,
    Functor.comp_obj] using congr_app hab K

private theorem open_compare_mono
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (k : X ⟶ Y) [IsOpenImmersion k]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) := by
  obtain ⟨L, ι, hi, _, ho, _⟩ := properSupportSheafComposition Λ
  have hι : Mono ((ι k).app F) := by
    refine ⟨fun {Z} a b hab ↦ ?_⟩
    ext V s
    apply (hi X Y k F V.unop).1
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun z ↦ z.hom) hab) V) s
  obtain ⟨o, he⟩ := ho X Y k
  have he' := congr_app he F
  dsimp only [NatTrans.comp_app] at he'
  rw [← he']
  infer_instance

private theorem ordinary_vertical (Λ : Type (u + 1)) [CommRing Λ]
    {A B C D E F : Scheme.{u}}
    (k : A ⟶ B) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j)
    (δ₁ : (r₁)_*[ModuleCat.{u + 1} Λ] ⋙ (i)_!open[ModuleCat.{u + 1} Λ] ≅
      (k)_!open[ModuleCat.{u + 1} Λ] ⋙ (p₁)_*[ModuleCat.{u + 1} Λ])
    (δ₂ : (r₂)_*[ModuleCat.{u + 1} Λ] ⋙ (j)_!open[ModuleCat.{u + 1} Λ] ≅
      (i)_!open[ModuleCat.{u + 1} Λ] ⋙ (p₂)_*[ModuleCat.{u + 1} Λ])
    (δ : (r₁ ≫ r₂)_*[ModuleCat.{u + 1} Λ] ⋙ (j)_!open[ModuleCat.{u + 1} Λ] ≅
      (k)_!open[ModuleCat.{u + 1} Λ] ⋙ (p₁ ≫ p₂)_*[ModuleCat.{u + 1} Λ])
    (hδ₁ : ∀ (X : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      δ₁.hom.app X ≫ (p₁)_*[ModuleCat.{u + 1} Λ].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k (p₁)).hom.app X =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app
        ((r₁)_*[ModuleCat.{u + 1} Λ].obj X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (r₁) i (k ≫ (p₁)) h₁).hom.app X)
    (hδ₂ : ∀ (X : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      δ₂.hom.app X ≫ (p₂)_*[ModuleCat.{u + 1} Λ].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) i (p₂)).hom.app X =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app
        ((r₂)_*[ModuleCat.{u + 1} Λ].obj X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (r₂) j (i ≫ (p₂)) h₂).hom.app X)
    (hδ : ∀ (X : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      δ.hom.app X ≫ (p₁ ≫ p₂)_*[ModuleCat.{u + 1} Λ].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k (p₁ ≫ p₂)).hom.app X =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app
        ((r₁ ≫ r₂)_*[ModuleCat.{u + 1} Λ].obj X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (r₁ ≫ r₂) j (k ≫ (p₁ ≫ p₂)) h).hom.app X)
    (X : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).map ((lowerStarComp (ModuleCat.{u + 1} Λ)
      r₁ r₂).hom.app X) ≫
        δ.hom.app X =
      δ₂.hom.app ((lowerStar (ModuleCat.{u + 1} Λ) r₁).obj X) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p₂).map (δ₁.hom.app X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂).hom.app ((openImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) k).obj X) := by
  have := open_compare_mono Λ k X
  apply (cancel_mono ((lowerStar (ModuleCat.{u + 1} Λ) (p₁ ≫ p₂)).map
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app X) ≫
    (lowerStarComp (ModuleCat.{u + 1} Λ) k (p₁ ≫ p₂)).hom.app X)).1
  simp only [Category.assoc]
  rw [hδ]
  have nc := (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂).hom.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app X)
  simp only [Functor.comp_map] at nc
  rw [← reassoc_of% nc]
  have hk := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ) k p₁ p₂ (k ≫ p₁) (p₁ ≫ p₂)
    (k ≫ (p₁ ≫ p₂)) rfl rfl (Category.assoc k p₁ p₂).symm) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hk
  rw [← hk, ← (lowerStar (ModuleCat.{u + 1} Λ) p₂).map_comp_assoc, ← (lowerStar (ModuleCat.{u + 1}
    Λ) p₂).map_comp_assoc]
  simp only [Category.assoc]
  rw [hδ₁]
  rw [(lowerStar (ModuleCat.{u + 1} Λ) p₂).map_comp]
  simp only [Category.assoc]
  have hi := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ) r₁ i p₂ (k ≫ p₁) (i ≫ p₂)
    (k ≫ (p₁ ≫ p₂)) h₁ rfl (Category.assoc k p₁ p₂).symm) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hi
  rw [hi, reassoc_of% hδ₂ ((lowerStar (ModuleCat.{u + 1} Λ) r₁).obj X)]
  have nj := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).naturality
    ((lowerStarComp (ModuleCat.{u + 1} Λ) r₁ r₂).hom.app X)
  rw [reassoc_of% nj]
  have hr := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ) r₁ r₂ j (r₁ ≫ r₂) (i ≫ p₂)
    (k ≫ (p₁ ≫ p₂)) rfl h₂ h) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hr
  rw [hr]

/-- The two pasting equations for normalized unbounded proper/open interchange.
Source: Stacks Project, Tags 0F7C and 0F7D.
(blueprint: lem-amb-unbounded-proper-open-composition).

Proof:
For the ordinary vertical equation, postcompose both sides with the support inclusion
into the common composite direct image. It is monic. Apply the assumed normalization
for each square, naturality of the direct-image compositor and of the open support
inclusion, and associativity of the direct-image compositors. This identifies the maps.
For the unbounded vertical equation, first treat six abstract abelian categories with
proper-edge functors G1,G2 and H1,H2 preserving K-injectives. Their iterated derived unit
is invertible on K-injectives and hence is a right-derivation unit, even after exact
extension by zero. Right-derived transformation uniqueness reduces the desired equality
to the unit equations. Expand the composite unit, move the square transformations past
the units by naturality, use the three assumed normalizations, and the two compositor
factorization equations. The ordinary equation then identifies the residual maps.
The geometric lowerStar compositors agree with these derived compositors because both
are conjugates of upperStar composition under the exact-inverse-image adjunctions.
Insert their inverses to obtain the displayed vertical equation. The horizontal equation
is the separate Tag 0F7D result, applied to the same normalized families.
-/
theorem unboundedProperOpenComposition_of_normalization (A : Type (u + 1)) [CommRing A] [Finite A]
    (θ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (Γ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]))
    (hθ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F))
    (hΓ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (X : HomotopyCategory
          (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)),
      ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategory.map
          (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app X) ≫
          (Γ k r p i sq).hom.app (DerivedCategory.Qh.obj X) =
        ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactorsh.hom.app
          ((((r)_*[ModuleCat.{u + 1} A]).mapHomotopyCategory (.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory (θ k r p i sq).hom (.up ℤ)).app X) ≫
          ((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
            ((((k)_!open[ModuleCat.{u + 1} A]).mapHomotopyCategory (.up ℤ)).obj X) ≫
          ((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctor.map
            (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactorsh.inv.app X))) :
    (∀ {U V W Z S T : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        [IsNoetherian S] [IsNoetherian T]
        (k : U ⟶ V) (r₁ : U ⟶ W) (p₁ : V ⟶ Z) (i₁ : W ⟶ Z)
        (r₂ : W ⟶ S) (p₂ : Z ⟶ T) (i₂ : S ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion i₁] [IsOpenImmersion i₂]
        [IsProper r₁] [IsProper p₁] [IsProper r₂] [IsProper p₂]
        (sq₁ : CommSq k r₁ p₁ i₁) (sq₂ : CommSq i₁ r₂ p₂ i₂)
        (K : DerivedCategoryModule A U),
        (Γ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂)).hom.app K =
          D((i₂)_!open[ModuleCat.{u + 1} A]).map
              ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r₁ r₂).inv.app K) ≫
            (Γ i₁ r₂ p₂ i₂ sq₂).hom.app (R((r₁)_*[ModuleCat.{u + 1} A]).obj K) ≫
            R((p₂)_*[ModuleCat.{u + 1} A]).map ((Γ k r₁ p₁ i₁ sq₁).hom.app K) ≫
            (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p₁ p₂).hom.app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj K)) ∧
    (∀ {U V T W Z S : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian T] [IsNoetherian W]
        [IsNoetherian Z] [IsNoetherian S]
        (k : U ⟶ V) (l : V ⟶ T) (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ S)
        (i : W ⟶ Z) (j : Z ⟶ S)
        [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
        [IsProper r] [IsProper p] [IsProper q]
        (sq₁ : CommSq k r p i) (sq₂ : CommSq l p q j)
        (K : DerivedCategoryModule A U),
        (Γ (k ≫ l) r q (i ≫ j) (sq₁.horiz_comp sq₂)).hom.app K =
          (Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app
              (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((j)_!open[ModuleCat.{u + 1} A]).map ((Γ k r p i sq₁).hom.app K) ≫
            (Γ l p q j sq₂).hom.app (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((q)_*[ModuleCat.{u + 1} A]).map
              ((Functor.mapDerivedCategoryNatIso
                  (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) k l) ≪≫
                (Functor.mapDerivedCategoryCompIso _ _).symm).inv.app K)) := by
  refine ⟨?_, unboundedProperOpenHorizontalComposition_of_normalization A θ Γ hθ hΓ⟩
  intro U V W Z S T _ _ _ _ _ _ k r₁ p₁ i₁ r₂ p₂ i₂ _ _ _ _ _ _ _ sq₁ sq₂ K
  exact generic_vertical_pasting
    (r₁)_*[ModuleCat.{u + 1} A] (r₂)_*[ModuleCat.{u + 1} A]
    (r₁ ≫ r₂)_*[ModuleCat.{u + 1} A]
    (p₁)_*[ModuleCat.{u + 1} A] (p₂)_*[ModuleCat.{u + 1} A]
    (p₁ ≫ p₂)_*[ModuleCat.{u + 1} A]
    (k)_!open[ModuleCat.{u + 1} A] (i₁)_!open[ModuleCat.{u + 1} A]
    (i₂)_!open[ModuleCat.{u + 1} A]
    (lowerStarComp (ModuleCat.{u + 1} A) r₁ r₂)
    (lowerStarComp (ModuleCat.{u + 1} A) p₁ p₂)
    (θ k r₁ p₁ i₁ sq₁).hom (θ i₁ r₂ p₂ i₂ sq₂).hom
    (θ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂)).hom
    (ordinary_vertical A k i₁ i₂ r₁ r₂ p₁ p₂ sq₁.w sq₂.w _
      (θ k r₁ p₁ i₁ sq₁) (θ i₁ r₂ p₂ i₂ sq₂)
      (θ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂))
      (hθ k r₁ p₁ i₁ sq₁) (hθ i₁ r₂ p₂ i₂ sq₂)
      (hθ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂)))
    (Γ k r₁ p₁ i₁ sq₁).hom (Γ i₁ r₂ p₂ i₂ sq₂).hom
    (Γ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂)).hom
    (hΓ k r₁ p₁ i₁ sq₁) (hΓ i₁ r₂ p₂ i₂ sq₂)
    (hΓ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂))
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r₁ r₂)
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p₁ p₂)
    (geometric_comp_fac A r₁ r₂) (geometric_comp_fac A p₁ p₂) K

end AlgebraicGeometry.Etale
