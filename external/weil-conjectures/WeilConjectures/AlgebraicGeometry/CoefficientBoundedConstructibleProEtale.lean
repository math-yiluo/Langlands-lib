/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-!
# Bounded constructible objects with discrete coefficients on the small site models

Stacks Project, Tags 09AJ and 09AL (blueprint: sk-def-sfb-bounded-constructible).

The existing general ring-object definition and its weak Serre triangulatedness statement
remain publicly available. This supplies their discrete constant-ring module presentation
on qcqs schemes and the equivalent coefficient-sized sites. It uses the existing
constructibility predicate
and ordinary derived localization, and retains all ambient derived morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- On a qcqs scheme, the discrete-coefficient presentation of `Dbc`: bounded cohomology and
the recorded
finite constant local models on every affine open. This is a predicate on the ordinary
standard derived localization, without any completeness condition.
Source: blueprint definition-constructible-sheaves and theorem-comparison-constructible-sheaves;
Stacks Tags 09AJ and 09AL (blueprint: sk-def-sfb-bounded-constructible). -/
def coefficientBoundedConstructibleProEtale (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :=
  fun K ↦
    (∀ q : ℤ, Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
      ((coefficientModelCohomology _ q).obj K)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((coefficientModelCohomology _ q).obj K)

end AlgebraicGeometry.ProEtale
