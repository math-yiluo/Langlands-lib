/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
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
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
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
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.QuasiIso
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
public import Mathlib.CategoryTheory.Adjunction.Limits
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
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
public import WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import WeilConjectures.RingTheory.LimitFlatModules
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
public import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
public import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
public import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
public import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
public import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
public import WeilConjectures.Algebra.Homology.InternalHom
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
public import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
public import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
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
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
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
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulQuotientComparison
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulQuotientAugmentationIsIso
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulQuotientAugmentation
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulAugmentationConstruction
public import WeilConjectures.CategoryTheory.TensorQuotientAugmentation
public import Mathlib.CategoryTheory.Abelian.Basic
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulLowDegrees
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
public import WeilConjectures.CategoryTheory.SignedKoszulFiniteCoordinates
public import WeilConjectures.CategoryTheory.SignedKoszulTensorCoordinates
public import WeilConjectures.CategoryTheory.SignedKoszulTensorCoproduct
public import WeilConjectures.CategoryTheory.SignedKoszulTensorAssembly
public import WeilConjectures.CategoryTheory.SignedKoszulBasisCoproduct
public import WeilConjectures.CategoryTheory.SignedKoszulSummandDifferential
public import WeilConjectures.CategoryTheory.SignedKoszulSummandTermTransport
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulTransitions
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulFactorHomTensor
public import WeilConjectures.AlgebraicGeometry.OrderedKoszulHomologyTorsion
public import WeilConjectures.Algebra.Homology.LocalizationCech.FlatLocalizationKoszulHomotopySupplement
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.AlgebraicGeometry.ConstantExactCoefficientRealization
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulCoefficientConeComparison
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import WeilConjectures.CategoryTheory.ExteriorKoszulScalarRealization
public import WeilConjectures.CategoryTheory.ExteriorKoszulBasisDifferential
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import WeilConjectures.CategoryTheory.RingedKoszulDualBasis
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulExteriorDifferential
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulSignedDifferential
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulBasisUnitor
public import WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
public import WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorConeComparison
public import WeilConjectures.AlgebraicGeometry.TensorConeTowerIso
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorSquare
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorIdentifications
public import WeilConjectures.AlgebraicGeometry.ConstantReductionTensorModel
public import WeilConjectures.AlgebraicGeometry.ConstantScalarTensorModel
public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantTensorNormalization
public import WeilConjectures.AlgebraicGeometry.ConstantTensorSingle
public import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorLevel
public import WeilConjectures.RingTheory.NoetherianKoszulAugmentationProZero
public import WeilConjectures.RingTheory.KoszulGeneratorChainMap
public import WeilConjectures.RingTheory.KoszulProjectiveResolution
public import WeilConjectures.RingTheory.KoszulPowerHomologyProZero
public import Mathlib.RingTheory.Filtration
public import WeilConjectures.RingTheory.KoszulConeHomologyProZero
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import WeilConjectures.Algebra.Homology.BoundedDerivedTowerProZero
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import WeilConjectures.CategoryTheory.Triangulated.ProZeroMiddle
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
public import WeilConjectures.CategoryTheory.Flat.FlatScalarKoszulModelsSupplement
import all WeilConjectures.CategoryTheory.Flat.FlatScalarKoszulTowerComparisonSupplement
import all WeilConjectures.CategoryTheory.Constant.ConstantTowerNormalization
import all WeilConjectures.CategoryTheory.RingedKFlatWord.RingedKFlatWordComparisonDescent
import WeilConjectures.CategoryTheory.Cochain.CochainUniversalCounitTransport
import WeilConjectures.CategoryTheory.Augmented.AugmentedDerivedTowerUnit
import all WeilConjectures.Algebra.Homology.DerivedQuotientTower.DerivedQuotientTowerPresentation
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Constant coefficient completion: Restriction

Restriction of the completions (`completion_restriction`) and of the Koszul comparison.

Part of the split of `WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe w

section D2Helpers
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory CochainComplex.IsAcyclicTensorKFlat
  CochainComplex.IsKFlatIndependentCoefficients
attribute [local irreducible] HasDerivedCategory.standard

namespace CategoryTheory.ConstantCompletion
private theorem transportCompletionUnit
    {B R : Type*} [Category B] [Category R]
    (F : B ⥤ R) (CB KB : B ⥤ B) (CR KR : R ⥤ R)
    (vB : 𝟭 B ⟶ CB) (vR : 𝟭 R ⟶ CR)
    (uB : ∀ M, M ⟶ KB.obj M) (uR : ∀ M, M ⟶ KR.obj M)
    (eR : KR ≅ CR) (eB : KB ≅ CB)
    (hR : ∀ N, uR N ≫ eR.hom.app N = vR.app N)
    (hB : ∀ M, uB M ≫ eB.hom.app M = vB.app M)
    (gamma : KB ⋙ F ≅ F ⋙ KR)
    (hg : ∀ M, F.map (uB M) ≫ gamma.hom.app M = uR (F.obj M)) :
    ∃ e : F ⋙ CR ≅ CB ⋙ F,
      ∀ M, vR.app (F.obj M) ≫ e.hom.app M = F.map (vB.app M) := by
  let e : F ⋙ CR ≅ CB ⋙ F := Functor.isoWhiskerLeft F eR.symm ≪≫
    gamma.symm ≪≫ Functor.isoWhiskerRight eB F
  refine ⟨e, ?_⟩
  intro M
  change vR.app (F.obj M) ≫
    (eR.inv.app (F.obj M) ≫ gamma.inv.app M ≫ F.map (eB.hom.app M)) = _
  rw [← hR, Category.assoc, eR.hom_inv_id_app_assoc]
  have hu : uR (F.obj M) ≫ gamma.inv.app M = F.map (uB M) := by
    rw [← hg M, Category.assoc, gamma.hom_inv_id_app]
    exact Category.comp_id _
  rw [← Category.assoc, hu, ← F.map_comp, hB]

end CategoryTheory.ConstantCompletion

namespace CategoryTheory.FlatScalarKoszul
variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}
variable [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules B)]
variable [HasDerivedCategory.{w} (Towers R)] [HasDerivedCategory.{w} (Towers B)]
private theorem arbitraryKoszulCompletion (φ : R ⟶ B)
    (hflat : PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor φ) ∧
      PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor φ))
    (r : ℕ) (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (DB : RingedKoszulLimitPresentation B r (imageSections φ a))
    (DR : RingedKoszulLimitPresentation R r a) :
    ∃ gamma : DB.completion ⋙ restrictDerived φ ≅ restrictDerived φ ⋙ DR.completion,
      ∀ E, (restrictDerived φ).map (DB.unit E) ≫ gamma.hom.app E =
        DR.unit ((restrictDerived φ).obj E) := by
  obtain ⟨h, _, hu⟩ := strictScalarKoszulComparison φ r a
  obtain ⟨hD, hd⟩ := descendedTensorComparison φ r a DB DR h
  obtain ⟨alpha, ha⟩ := normalizedLimitComparison φ hflat r a DB DR
  let gamma : DB.completion ⋙ restrictDerived φ ≅ restrictDerived φ ⋙ DR.completion :=
    Functor.isoWhiskerLeft DB.tensorTower alpha ≪≫
      Functor.isoWhiskerRight hD DR.inverseLimit
  refine ⟨gamma, ?_⟩
  intro E
  apply unitCompatibility_of_Q φ r a DB DR gamma _ E
  intro N
  have hN := derivedUnitRestrictionOnComplex φ r a DB DR h hD hd alpha ha hu N
  dsimp only [gamma, RingedKoszulLimitPresentation.completion, Functor.comp_obj,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hN ⊢
  simpa only [Category.assoc] using hN
end CategoryTheory.FlatScalarKoszul

end D2Helpers

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation

private theorem chosenKoszulRestriction [IsNoetherianRing A]
    (r : ℕ) (a : Fin r → A)
    (KB : KoszulPresentation J A I true r a)
    (KR : KoszulPresentation J A I false r a) :
    ∃ gamma : koszulCompletion J A I KB ⋙ dres (coefficientMap J A I) ≅
        dres (coefficientMap J A I) ⋙ koszulCompletion J A I KR,
      ∀ M, (dres (coefficientMap J A I)).map (koszulUnit J A I KB M) ≫
        gamma.hom.app M = koszulUnit J A I KR ((dres (coefficientMap J A I)).obj M) := by
  let := HasDerivedCategory.standard (Mod (constant J A))
  let := HasDerivedCategory.standard (Mod (completed J A I))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (constant J A))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (completed J A I))
  have hf := change_exact (coefficientMap J A I) (flat_and_quotients J A I).1
  exact FlatScalarKoszul.arbitraryKoszulCompletion
    (coefficientMap J A I) hf r
    (fun i ↦ algebraSection (baseMap J A I false) (a i)) KB KR

/-- Restriction identifies both completions and their specified units.
Source: Stacks 099L, 099M (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: at the representative level finite reduction comparisons and dual Koszul tensor
comparisons preserve their strict transitions and degree-zero units. Restriction carries
K-injective strict tower resolutions to K-injective resolutions, since it is right
adjoint to flat exact extension of scalars. Apply limits and the universal comparisons.
This gives the natural isomorphism and the stated equality of the actual units. -/
theorem completion_restriction [IsNoetherianRing A] :
    ∃ e : dres (coefficientMap J A I) ⋙ completion J A I false ≅
        completion J A I true ⋙ dres (coefficientMap J A I),
      ∀ M : D (completed J A I),
        (completionUnit J A I false).app ((dres (coefficientMap J A I)).obj M) ≫
          e.hom.app M =
        (dres (coefficientMap J A I)).map ((completionUnit J A I true).app M) := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    I.fg_of_isNoetherianRing
  obtain ⟨KR, ⟨eR, heR⟩, _⟩ := koszul_quotient_reflector J A I false r a ha
  obtain ⟨KB, ⟨eB, heB⟩, _⟩ := koszul_quotient_reflector J A I true r a ha
  obtain ⟨gamma, hg⟩ := chosenKoszulRestriction J A I r a KB KR
  exact transportCompletionUnit (dres (coefficientMap J A I))
    (completion J A I true) (koszulCompletion J A I KB)
    (completion J A I false) (koszulCompletion J A I KR)
    (completionUnit J A I true) (completionUnit J A I false)
    (koszulUnit J A I KB) (koszulUnit J A I KR) eR eB heR heB gamma hg

end CategoryTheory.ConstantCompletion
