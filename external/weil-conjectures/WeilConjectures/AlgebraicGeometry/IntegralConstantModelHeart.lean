/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import Mathlib.CategoryTheory.Abelian.Subcategory
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleModuleObjectsEssentiallySmall
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# The integral constant-model constructible category and its heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-integral-heart/
sk-lem-int-integral-heart-triangulated.md, assertions 1--2
(blueprint: lemma-structure-integral-constructible-complexes--1).

Coefficients are pulled-back condensed continuous functions into the valuation ring,
and the derived category is the ordinary unbounded category of internal modules.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The condensed valuation ring for an arbitrary finite extension, using its canonical
spectral norm. A finite extension of the small field of p-adic numbers is small by
`Module.Finite.small`. Its `Shrink` is used only to fit the existing continuous-function
API; `Shrink.algEquiv` identifies it with the given extension. Thus no coefficient
embedding or equality of universes is assumed. Source: blueprint integral-heart setting
and def-weil-l-adic-coefficient-extension
(blueprint: lemma-structure-integral-constructible-complexes--1). -/
noncomputable abbrev integralHeartCoefficientRingObj
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : Small.{0} E := Module.Finite.small (Padic ℓ) E
  letI : FiniteDimensional (Padic ℓ) (Shrink.{0} E) :=
    (Shrink.algEquiv (Padic ℓ) E).symm.toLinearEquiv.finiteDimensional
  letI := spectralNorm.normedField (Padic ℓ) (Shrink.{0} E)
  Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers ℓ (Shrink.{0} E))

end AlgebraicGeometry.ProEtale
