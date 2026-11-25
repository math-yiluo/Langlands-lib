/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.AlgebraicGeometry.ExtendedCechReflectorCore
import all WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import all WeilConjectures.CategoryTheory.RingedIdealGenerators
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.CategoryTheory.LocalExtendedCechDescription
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteUnitCriterion
import all WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteImpliesUnitIso
import all WeilConjectures.CategoryTheory.RingedCechCompletionUnitIdempotence
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import all WeilConjectures.Algebra.Homology.KFlatRHomCurrying
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import all WeilConjectures.Algebra.Homology.HomTensorDegreewise
import all WeilConjectures.Algebra.Homology.HomTensorDifferential
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import all WeilConjectures.Algebra.Homology.HomTensorNaturality
import all WeilConjectures.CategoryTheory.RingedCechTensorIdempotence
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Tactic.Basic
import all WeilConjectures.CategoryTheory.RingedLocalizationFactorTensorAugmentation
import all WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all Mathlib.Algebra.Homology.HomologySequenceLemmas
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import all Mathlib.RingTheory.Localization.BaseChange
import all WeilConjectures.CategoryTheory.Ringed.RingedLocalizationModelsSupplement
import all WeilConjectures.Algebra.Homology.KFlatComparison
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.RingedInternalHomContravariantExact
import all Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import all WeilConjectures.Algebra.Homology.SixFunctors.BifunctorHomHomotopyExactSupplement
import all WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import all Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
import all WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft
import all WeilConjectures.AlgebraicGeometry.FiniteIdealGeneratingCover
import all Mathlib.Data.Fintype.EquivFin
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Mathlib.CategoryTheory.Sites.LocalProperties
import all WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc
import all WeilConjectures.AlgebraicGeometry.ExtendedCechUnitIsoImpliesComplete
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import all WeilConjectures.CategoryTheory.RingedSiteLocalization
import all Mathlib.CategoryTheory.Sites.LeftExact
import all WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import all WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import all Mathlib.RingTheory.Ideal.Span
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import all WeilConjectures.Algebra.Homology.HomTensorTotal
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import all WeilConjectures.CategoryTheory.RingedSiteLocalizationCech
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Preadditive.Biproducts
import all WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import all Mathlib.Algebra.Category.ModuleCat.Colimits
import all Mathlib.Algebra.Module.LocalizedModule.Basic
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all WeilConjectures.RingTheory.TwoLocalizationExact
import all Mathlib.RingTheory.Coprime.Lemmas
import all Mathlib.Algebra.Exact.Basic
import all Mathlib.Tactic.LinearCombination
import all Mathlib.Tactic.Ring
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal
import all WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import all WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import all WeilConjectures.CategoryTheory.SliceAwayLocalizationFreeResolution
import all WeilConjectures.CategoryTheory.SliceAwayLocalization
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.RingTheory.Flat.Localization
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.AlgebraicGeometry.FiniteGeneratorsLocalSpan
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Abelian.Exact
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.Augmented.AugmentedCechObjectPullback
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonIndependent

/-! # Pullback of augmented extended Cech tensor actions

Source: Stacks Project, algebraization.tex, Tag 0A0G, the final pullback identity,
and sites-cohomology.tex, Tags 07A4 and 08J9.
(blueprint: lem-weil-pbc-augmented-cech-tensor-pullback).
-/

@[expose] public section

set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u wX wY

open CategoryTheory CategoryTheory.Limits WeilConjectures
open scoped MonoidalCategory

namespace CategoryTheory

end CategoryTheory
