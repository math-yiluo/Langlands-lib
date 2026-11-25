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
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.RingTheory.Ideal.Quotient.PowTransition
import all Mathlib.RingTheory.Noetherian.Defs
import all Mathlib.RingTheory.Ideal.Quotient.Operations
import all WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import all Mathlib.RingTheory.Ideal.Maps
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all Mathlib.CategoryTheory.Sites.Over
import all WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import all WeilConjectures.CategoryTheory.RingedIdealGenerators
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
import all WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import all Mathlib.Algebra.Category.ModuleCat.Limits
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all Mathlib.Algebra.Module.FinitePresentation
import all Mathlib.RingTheory.Flat.Basic
import all Mathlib.RingTheory.Flat.Tensor
import all Mathlib.LinearAlgebra.TensorProduct.RightExactness
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.CategoryTheory.Linear.FunctorCategory
import all Mathlib.CategoryTheory.Linear.LinearFunctor
import all WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
import all Mathlib.CategoryTheory.Limits.Over
import all Mathlib.Algebra.Category.CommAlgCat.Basic
import all WeilConjectures.RingTheory.LimitFlatModules
import all Mathlib.RingTheory.Flat.EquationalCriterion
import all Mathlib.RingTheory.TensorProduct.Quotient
import all Mathlib.RingTheory.Ideal.Quotient.Noetherian
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
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
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Finiteness.Defs
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import all Mathlib.CategoryTheory.Adjunction.Whiskering
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all Mathlib.CategoryTheory.Limits.Final
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage

/-!
# Constant coefficient completion: InverseImage

Tower restriction, derived limit restriction, inverse-image data and ringed pullbacks.

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

variable {J A I}

/-- The exact levelwise restriction comparison on strict tower complexes.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tresFactors {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ TQ R ≅ TQ B ⋙ tdres φ :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (tres φ).mapDerivedCategoryFactors.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [instance] restrictionReduction_additive

attribute [instance] reductionRestriction_additive

attribute [instance] reductionRestriction_preservesZero

-- Use the generic composite-functor instances while elaborating the remaining proofs.
-- Restore the exported instances at the end of the module.
attribute [-instance] restrictionReduction_additive reductionRestriction_additive
  reductionRestriction_preservesZero

section
attribute [local irreducible] dres change

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary inverse limits commute with scalar restriction by their coordinate maps.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: module restriction preserves limits, computed on underlying additive sheaves.
The limit comparison is invertible degreewise and commutes with differentials. Its
coordinate equations determine it uniquely, so this is a canonical chain isomorphism. -/
theorem limitRestriction_existsUnique {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    ∃! e : ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R,
      ∀ (P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ) (q : ℤ) (n : ℕ),
        (e.hom.app P).f q ≫
          limit.π (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P |>.X q) (op n) =
        (res φ).map (limit.π (P.X q) (op n)) := by
  have : PreservesLimitsOfSize.{u, u} (res φ) := siteRestrictScalars_preservesLimits φ
  have : PreservesLimitsOfSize.{0, 0} (res φ) := preservesLimitsOfSize_shrink (res φ)
  let liftIso {A₀ A₁ A₂ A₃ : Type (u + 1)}
      [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂] [Category.{u} A₃]
      [Preadditive A₀] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
      (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₃) (H : A₀ ⥤ A₂) (K : A₂ ⥤ A₃)
      [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          G.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          K.mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ K)) (ComplexShape.up ℤ)).symm
  have liftIso_hom_f {A₀ A₁ A₂ A₃ : Type (u + 1)}
      [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂] [Category.{u} A₃]
      [Preadditive A₀] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
      (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₃) (H : A₀ ⥤ A₂) (K : A₂ ⥤ A₃)
      [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K)
      (P : CochainComplex A₀ ℤ) (q : ℤ) :
      ((liftIso F G H K e).hom.app P).f q = e.hom.app (P.X q) := by
    dsimp only [liftIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex, NatTrans.comp_app, HomologicalComplex.comp_f]
    simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    exact (Category.id_comp _).trans (Category.comp_id _)
  have : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R).Additive :=
    Functor.additive_of_preserves_binary_products _
  let α : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B) ⋙ res φ ≅
      tres φ ⋙ (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R) := preservesLimitNatIso (res φ)
  let e : ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R :=
    liftIso (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B) (res φ) (tres φ)
      (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R) α
  have he (P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ) (q : ℤ) (n : ℕ) :
      (e.hom.app P).f q ≫
        limit.π (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P |>.X q) (op n) =
      (res φ).map (limit.π (P.X q) (op n)) := by
    change ((liftIso _ _ _ _ α).hom.app P).f q ≫ _ = _
    rw [liftIso_hom_f]
    exact preservesLimitIso_hom_π (res φ) (P.X q) (op n)
  refine ⟨e, he, ?_⟩
  intro g hg
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro q
  apply limit.hom_ext
  intro n
  exact (hg P q n.unop).trans (he P q n.unop).symm

/-- The ordinary limit comparison fixed by its actual projections. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def limitRestriction {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R :=
  (limitRestriction_existsUnique φ).exists.choose

section ExactScalarExtension
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The proved extension-tensor comparison, selected once for each module. -/
private def extensionTensorComponent {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (M : Mod R) :
    (SheafOfModules.monoidalCategory R).tensorObj
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) M ≅
        (res φ).obj ((change φ).obj M) :=
  (SheafOfModules.exists_extensionTensorComparison φ M).choose

/-- Its section formula is the original balanced tensor map. -/
private theorem extensionTensorComponent_pure {R B : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (M : Mod R) (U : Cᵒᵖ) (s : B.obj.obj U) (m : M.val.obj U) :
    (extensionTensorComponent φ M).hom.val.app U
        (SheafOfModules.RingedTensor.pure R
          ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) M U s m) =
      tensorSection φ M U s m :=
  (SheafOfModules.exists_extensionTensorComparison φ M).choose_spec U s m

attribute [irreducible] extensionTensorComponent

/-- The pure-tensor comparison is natural in the module argument.
Source: Stacks 03EK; the component is exists_extensionTensorComparison. -/
private def extensionTensorIso {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    letI := SheafOfModules.monoidalCategory R
    MonoidalCategory.tensorLeft ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) ≅
      change φ ⋙ res φ := by
  letI := SheafOfModules.monoidalCategory R
  let N := (res φ).obj (SheafOfModules.unit (siteModuleRings B))
  refine NatIso.ofComponents (extensionTensorComponent φ) ?_
  intro M M' f
  apply SheafOfModules.RingedTensor.pure_hom_ext R N M
  intro U s m
  change (extensionTensorComponent φ M').hom.val.app U
      ((MonoidalCategory.whiskerLeft N f).val.app U
        (SheafOfModules.RingedTensor.pure R N M U s m)) =
    ((change φ).map f).val.app U
      ((extensionTensorComponent φ M).hom.val.app U
        (SheafOfModules.RingedTensor.pure R N M U s m))
  rw [← MonoidalCategory.id_tensorHom, SheafOfModules.RingedTensor.pure_map]
  change (extensionTensorComponent φ M').hom.val.app U
      (SheafOfModules.RingedTensor.pure R N M' U s (f.val.app U m)) = _
  rw [extensionTensorComponent_pure, extensionTensorComponent_pure]
  exact (tensorSection_map φ f U s m).symm

/-- Flatness of the target ring makes scalar extension exact.
Source: Stacks 03EK. Identify its restriction with tensoring by the flat target,
reflect finite limits through restriction, and use the extension adjunction for colimits. -/
private theorem change_exact {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (hflat : SheafOfModules.IsFlat
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B)))) :
    PreservesFiniteLimits (change φ) ∧ PreservesFiniteColimits (change φ) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let N := (res φ).obj (SheafOfModules.unit (siteModuleRings B))
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight N) := hflat.1
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft N) :=
    preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight N).symm
  have : PreservesFiniteLimits (change φ ⋙ res φ) :=
    preservesFiniteLimits_of_natIso (extensionTensorIso φ)
  have : (res φ).ReflectsIsomorphisms := siteRestrictScalars_reflectsIsomorphisms φ
  have : PreservesFiniteLimits (res φ) := (siteRestrictScalars_exact φ).1
  have : ReflectsFiniteLimits (res φ) :=
    { reflects := fun K _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  have hleft : PreservesFiniteLimits (change φ) :=
    preservesFiniteLimits_of_reflects_of_preserves (change φ) (res φ)
  have : PreservesColimitsOfSize.{0, 0} (change φ) :=
    (SheafOfModules.RingedTensor.tensorAdjunction φ).leftAdjoint_preservesColimits
  have hright : PreservesFiniteColimits (change φ) := inferInstance
  exact ⟨hleft, hright⟩

end ExactScalarExtension

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact restriction/limit square derives by the tower adjunction.
The abstract ring parameters prevent elaboration from unfolding a completion limit. -/
private theorem derivedLimitRestriction_of_flat {R B : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (hflat : SheafOfModules.IsFlat
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B)))) :
    ∃ e : rlim B ⋙ dres φ ≅
        tdres φ ⋙ rlim R,
      ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ,
        (dres φ).map ((limitComparison B).app P) ≫
          e.hom.app ((TQ B).obj P) =
        (resFactors φ).inv.app
            ((ordinaryLimit B).obj P) ≫
          (Q R).map ((limitRestriction φ).hom.app P) ≫
          (limitComparison R).app
            (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (rlim R).map ((tresFactors φ).hom.app P) := by
  let : Abelian (Mod R) :=
    { (inferInstance : Abelian (Mod R)) with
      toPreadditive := (inferInstance : Preadditive (Mod R)) }
  let : Abelian (Mod B) :=
    { (inferInstance : Abelian (Mod B)) with
      toPreadditive := (inferInstance : Preadditive (Mod B)) }
  let : Abelian (ℕᵒᵖ ⥤ Mod R) :=
    { (inferInstance : Abelian (ℕᵒᵖ ⥤ Mod R)) with
      toPreadditive := (inferInstance : Preadditive (ℕᵒᵖ ⥤ Mod R)) }
  let : Abelian (ℕᵒᵖ ⥤ Mod B) :=
    { (inferInstance : Abelian (ℕᵒᵖ ⥤ Mod B)) with
      toPreadditive := (inferInstance : Preadditive (ℕᵒᵖ ⥤ Mod B)) }
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod B)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ Mod B) := by
    have := smallModuleDiagrams_isGrothendieckAbelian J (siteModuleRings B)
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  have hex := change_exact φ hflat
  have : PreservesFiniteLimits (change φ) := hex.1
  have : PreservesFiniteColimits (change φ) := hex.2
  let E := (Functor.whiskeringRight ℕᵒᵖ (Mod R) (Mod B)).obj (change φ)
  have : E.Additive := inferInstance
  have : PreservesFiniteLimits E := ⟨fun K _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits E := ⟨fun K _ _ ↦ inferInstance⟩
  have : E.PreservesHomology := {}
  have adj : E ⊣ tres φ :=
    Adjunction.whiskerRight ℕᵒᵖ (SheafOfModules.RingedTensor.tensorAdjunction φ)
  have : (tres φ).PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  have : PreservesLimitsOfSize.{u, u} (res φ) := siteRestrictScalars_preservesLimits φ
  have : PreservesLimitsOfSize.{0, 0} (res φ) := preservesLimitsOfSize_shrink (res φ)
  have : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R).Additive :=
    Functor.additive_of_preserves_binary_products _
  let c : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B) ⋙ res φ ≅
      tres φ ⋙ (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R) := preservesLimitNatIso (res φ)
  obtain ⟨e, he⟩ := towerComparison_existsLimitIso (res φ) (dres φ) (tdres φ)
    (rlim B) (rlim R) (resFactors φ).hom (tresFactors φ).hom
    (limitComparison B) (limitComparison R)
    (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance)
    (strictLimit B).computation
    (fun P hP ↦ by
      have := hP
      change IsIso ((limitComparison R).app
        (((tres φ).mapHomologicalComplex (.up ℤ)).obj P))
      exact (strictLimit R).computation _ inferInstance) c
  refine ⟨e, ?_⟩
  intro P
  have h := he P
  have hc : (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P =
      (limitRestriction φ).hom.app P := by
    apply HomologicalComplex.hom_ext
    intro q
    apply limit.hom_ext
    intro n
    change c.hom.app (P.X q) ≫ limit.π _ n = _
    exact (preservesLimitIso_hom_π (res φ) (P.X q) n).trans
      ((limitRestriction_existsUnique φ).exists.choose_spec P q n.unop).symm
  rw [hc] at h
  apply (cancel_epi ((resFactors φ).hom.app ((ordinaryLimit B).obj P))).mp
  change (resFactors φ).hom.app ((ordinaryLimit B).obj P) ≫
      (dres φ).map ((limitComparison B).app P) ≫ e.hom.app ((TQ B).obj P) =
    (resFactors φ).hom.app ((ordinaryLimit B).obj P) ≫
      (resFactors φ).inv.app ((ordinaryLimit B).obj P) ≫
        (Q R).map ((limitRestriction φ).hom.app P) ≫
          (limitComparison R).app (((tres φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
            (rlim R).map ((tresFactors φ).hom.app P)
  rw [Iso.hom_inv_id_app_assoc]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction identifies total right derived limits of strict towers, canonically.
The comparison is normalized by the ordinary limit coordinate comparison and both
right-derived universal transformations. Source: Stacks 0940 and 0A07
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: extension of scalars is exact by flat_and_quotients, and restriction is its exact
right adjoint. This adjunction holds levelwise on strict towers, so the right-adjoint
K-injective theorem sends a K-injective tower resolution to one over the constant ring.
Ordinary limits agree by their coordinates. Apply the universal right-derived
comparisons to obtain the natural isomorphism and its displayed normalization. -/
theorem derivedLimitRestriction (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : rlim (completed J A I) ⋙ dres (coefficientMap J A I) ≅
        tdres (coefficientMap J A I) ⋙ rlim (constant J A),
      ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (completed J A I)) ℤ,
        (dres (coefficientMap J A I)).map ((limitComparison (completed J A I)).app P) ≫
          e.hom.app ((TQ (completed J A I)).obj P) =
        (resFactors (coefficientMap J A I)).inv.app
            ((ordinaryLimit (completed J A I)).obj P) ≫
          (Q (constant J A)).map ((limitRestriction (coefficientMap J A I)).hom.app P) ≫
          (limitComparison (constant J A)).app
            (((tres (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (rlim (constant J A)).map ((tresFactors (coefficientMap J A I)).hom.app P) := by
  exact derivedLimitRestriction_of_flat (coefficientMap J A I)
    (flat_and_quotients J A I).1

/-- A sheaf map with a fixed section formula is unique. -/
private theorem sheaf_map_existsUnique_of_formula {X Y : Sheaf J (Type u)}
    (q : X ⟶ Y) (f : ∀ U : Cᵒᵖ, X.obj.obj U → Y.obj.obj U)
    (hq : ∀ U x, q.hom.app U x = f U x) :
    ∃! q' : X ⟶ Y, ∀ U x, q'.hom.app U x = f U x := by
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro m
  exact (hq' U m).trans (hq U m).symm

variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}

variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

set_option backward.isDefEq.respectTransparency false in
attribute [local semireducible] completed

attribute [local irreducible] completed

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Addition transport and underlying naturality make the algebraic module lift additive.
Abstracting the lift avoids repeatedly reducing the full inverse-image data record. -/
private theorem algebraModules_additive {R : Sheaf J CommRingCat.{u}}
    {RI : Sheaf J' CommRingCat.{u}}
    (AI : SheafOfModules.AlgebraicInverseImage L R RI) : AI.modules.Additive := by
  constructor
  intro M N f g
  ext U x
  let e := AI.moduleUnderlying
  let y := (e.hom.app M).hom.app U x
  have hy : (e.inv.app M).hom.app U y = x :=
    congrFun (congrArg (fun t ↦ t.hom.app U) (e.hom_inv_id_app M)) x
  have hn (k : M ⟶ N) :
      (e.inv.app N).hom.app U ((L.map ((underlying R).map k)).hom.app U y) =
        (AI.modules.map k).val.app U x := by
    have hh := congrFun
      (congrArg (fun t ↦ t.hom.app U) (e.inv.naturality k)) y
    change _ = (AI.modules.map k).val.app U
      ((e.inv.app M).hom.app U y) at hh
    exact hh.trans (congrArg ((AI.modules.map k).val.app U) hy)
  have h := AI.moduleAdd N ((underlying R).obj M)
    ((underlying R).map f) ((underlying R).map g) ((underlying R).map (f + g))
    (fun _ _ ↦ rfl) U y
  exact (hn (f + g)).symm.trans
    (h.trans (congrArg₂ (fun (a b : (AI.modules.obj N).val.obj U) ↦ a + b)
      (hn f) (hn g)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [instance] pull_additive

variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The live K-flat and monoidal-flat interface for a prescribed ringed pullback. -/
private theorem basechange_flat_kFlat
    {R : Sheaf J CommRingCat.{u}} {RI S : Sheaf J' CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u))
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (AI : SheafOfModules.AlgebraicInverseImage L R RI)
    (c : RI ⟶ S) (T : Mod R ⥤ Mod S) [T.Additive]
    (ho : ∀ M : Mod R, T.obj M = SheafOfModules.changeOfRings c (AI.modules.obj M))
    (hm : ∀ {M N : Mod R} (f : M ⟶ N), T.map f = eqToHom (ho M) ≫
      SheafOfModules.changeOfRingsHom c (AI.modules.obj M) (AI.modules.map f) ≫
        eqToHom (ho N).symm)
    (P : Cx R) (hP : P.IsAcyclicTensorKFlat)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsAcyclicTensorKFlat
      ((T.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, SheafOfModules.IsFlat (T.obj (P.X q)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  have hf' (q : ℤ) := (exactFunctor (Mod R) (Mod R)).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X q)).symm (hf q)
  obtain ⟨hk, hflat⟩ := SheafOfModules.isKFlat_ringedToposPullback L V adj
    AI c T ho hm P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) hf'
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
  intro q
  exact (exactFunctor (Mod S) (Mod S)).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso S (T.obj (P.X q))) (hflat q)

include V adj hL in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pull_flat_kFlat {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} (c : F.rings.obj R ⟶ S) (P : Cx R)
    (hP : P.IsAcyclicTensorKFlat) (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsAcyclicTensorKFlat
      (((pull F c).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, SheafOfModules.IsFlat ((pull F c).obj (P.X q)) := by
  have ho (M : Mod R) : (pull F c).obj M =
      SheafOfModules.changeOfRings c ((F.algebra R).modules.obj M) := rfl
  have hm {M N : Mod R} (f : M ⟶ N) : (pull F c).map f =
      eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom c
        ((F.algebra R).modules.obj M) ((F.algebra R).modules.map f) ≫
          eqToHom (ho N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  exact basechange_flat_kFlat L V adj (F.algebra R) c (pull F c) ho hm P hP hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem change_flat_kFlat {R S : Sheaf J CommRingCat.{u}}
    (c : R ⟶ S) (P : Cx R) (hP : P.IsAcyclicTensorKFlat)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsAcyclicTensorKFlat
      (((change c).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, SheafOfModules.IsFlat ((change c).obj (P.X q)) := by
  have ho (M : Mod R) : (change c).obj M = SheafOfModules.changeOfRings c M := rfl
  have hm {M N : Mod R} (f : M ⟶ N) : (change c).map f =
      eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom c M f ≫
        eqToHom (ho N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨hk, hflat⟩ :=
    SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      c P (change c) ho hm
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) hf
  exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, hflat⟩

attribute [local irreducible] derivedPull pull change

end CategoryTheory.ConstantCompletion
