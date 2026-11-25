/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Classical finite-coefficient derived category

Source: the current blueprint, `definition-classical-pro-etale-sheaves`, final complex clause
(blueprint: def-sfb-classical-derived-category).

For a finite discrete coefficient ring, this is the full subcategory of the unbounded
pro-etale derived category whose cohomology module sheaves satisfy the classical
continuity-map condition.  The ambient objects and all morphisms are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- `D_class(T_proet, A)` as the full subcategory on complexes with classical
cohomology sheaves (blueprint: def-sfb-classical-derived-category). -/
abbrev classicalDerivedCategory (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  ObjectProperty.FullSubcategory (IsClassicalComplexFor T A)

end AlgebraicGeometry.ProEtale
