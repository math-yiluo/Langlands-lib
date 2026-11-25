/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility

/-!
# Constructibility with finite constant scalar models

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sfb-constructible,
clauses 1--2 and the final paragraph (blueprint: definition-constructible-sheaves).

A finite presentation over the condensed ring on the point is a finite matrix over
its scalar ring: maps between copies of the regular module are global sections of
the condensed ring. Pulling its cokernel to a scheme therefore gives precisely the
scalar-extension model in the source. The matrix is chosen on the point, before any
scheme restriction, so arbitrary local coefficient functions are not admitted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

open Classical in
/-- The full subcategory Cons of constructible module sheaves with finite constant models.
Source: blueprint definition-constructible-sheaves, final paragraph
(blueprint: definition-constructible-sheaves). -/
abbrev ConstantModelConstructible (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (IsConstantModelConstructible Λ X)


end AlgebraicGeometry.ProEtale
