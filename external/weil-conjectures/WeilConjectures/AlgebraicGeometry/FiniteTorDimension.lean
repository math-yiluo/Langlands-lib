/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes

/-! # Finite Tor dimension on a scheme

Source: Stacks Project, Cohomology of Sheaves, Definition 20.48.1, Tag 08CG
(blueprint: def-pc-finite-tor-dimension).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A derived object has finite Tor dimension when one finite interval bounds the
cohomology of its derived tensor with every module sheaf. The interval is global,
independent of the test module. Source: Stacks Project, Definition 20.48.1 (08CG)
(blueprint: def-pc-finite-tor-dimension). -/
def HasFiniteTorDimension (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧
    ∀ F : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X E F i

end AlgebraicGeometry.Scheme
