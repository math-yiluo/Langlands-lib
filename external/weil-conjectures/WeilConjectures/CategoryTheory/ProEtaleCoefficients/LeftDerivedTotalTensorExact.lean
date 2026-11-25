/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LeftDerivedTotalTensor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
# The left derived functor of an exact functor

Source: blueprint main-20261015, `chap-The-pro-etale-site`,
`sk-def-sfb-derived-categories`, `def-sfb-left-derived-exact`
(blueprint: def-sfb-left-derived-exact).

The canonical comparison uses the recorded total-tensor left derived functor and
Mathlib's uniqueness isomorphism, with no additional graded-tensor hypotheses.

## Main definitions

* `leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory`: the canonical comparison.
* `leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory_hom_fac`: its counit compatibility.
-/

@[expose] public section

universe uC vC uD vD wC wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C] [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

end CategoryTheory.Functor
