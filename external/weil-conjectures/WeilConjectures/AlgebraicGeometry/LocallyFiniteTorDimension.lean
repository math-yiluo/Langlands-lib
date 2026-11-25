/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.AlgebraicGeometry.DerivedPullback

/-! # Locally finite Tor dimension on schemes

Source: Stacks Project, Cohomology of Sheaves, Definition 08CG
(cohomology-definition-tor-amplitude) (blueprint: def-pc-locally-finite-tor-dimension).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- `E` locally has finite Tor dimension: every point has an open neighbourhood `U`
and integers `a ≤ b` such that `H^i(E|_U ⊗ᴸ G) = 0` for every `𝒪_U`-module `G` and
every `i ∉ [a, b]`. Here `E|_U` is the derived pullback along the open immersion
`U.ι`, and the vanishing is the scheme predicate
`schemeDerivedTensorCohomologyVanishes` (a K-flat representative whose total tensor
with `G[0]` has zero cohomology in degree `i`; Stacks Tags 06YS and 06YU).
Source: Stacks Project, Definition 08CG (cohomology-definition-tor-amplitude), clause (3)
(blueprint: def-pc-locally-finite-tor-dimension). -/
def HasLocallyFiniteTorDimension (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a b : ℤ, a ≤ b ∧
    ∀ (G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (i : ℤ),
      i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes U.toScheme ((derivedPullback U.ι).obj E) G i

end AlgebraicGeometry.Scheme
