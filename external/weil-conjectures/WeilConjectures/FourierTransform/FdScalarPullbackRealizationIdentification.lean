/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.FourierTransform.FdPullbackComparison
import WeilConjectures.FourierTransform.FdPullbackAugmentationCounitMatching
public import WeilConjectures.FourierTransform.PullbackCommonStrictTowerModels
public import WeilConjectures.SixFunctors.Supporting.SpecifiedPullbackComparisonAlpha
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
import WeilConjectures.CategoryTheory.Finite.FiniteFreeStrictTowerTransport
import WeilConjectures.CategoryTheory.Finite.FiniteFreeCompletionTransport
import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.Algebra.Homology.Strict.StrictProjectionLimitData

import WeilConjectures.TraceFormula.CounitRealization.CounitRealizationSubstitution
import WeilConjectures.AlgebraicGeometry.Integral.IntegralComparisonCounitCharacterization
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
import WeilConjectures.CategoryTheory.ReflectedCoefficient.Arrow.ReflectedAdjunctionCoefficientSquares
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Identification of scalar pullback realization maps

Source: blueprint, trace-definition coefficient-category identification;
Stacks Tags 0941 and 099N(5)
(blueprint: lem-fd-scalar-pullback-realization-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

end WeilConjectures
