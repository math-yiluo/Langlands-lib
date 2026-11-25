/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-!
# Coefficient conventions for smooth base change

Source: literature/blueprint/master/blueprint/sec-smooth-base-change/sk-def-bc/
`sbc-def-coefficient-conventions.md` (blueprint: sbc-def-coefficient-conventions).

The coefficient hypotheses are collected in `Etale.IsSmoothBaseChangeCoefficients`.
All sheaf and derived notions are the imported ambient-foundation notions:

* `Mod(T_et, Λ)` is `CategoryTheory.Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
* Torsion is `CategoryTheory.Sheaf.IsTorsion`; lisse and constructible module sheaves use
  `Scheme.IsFiniteLocallyConstantSheaf` and
  `Scheme.IsConstructibleEtaleModuleSheaf`.
* `D(T_et, Λ)` is `Etale.DerivedCategoryModule Λ T`; `D⁺` is `DerivedCategory.Plus`
  of the same module-sheaf category.
* K-injective resolutions are `CochainComplex.IsKInjectiveResolution`.
* `Dᵇc(T_et, Λ)` is `Etale.BoundedConstructibleDerivedCategory Λ T`.

These conventions introduce no new sheaf category, constructibility predicate or resolution.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Etale

/-- The coefficient convention for smooth base change: `N` is positive, `Λ` is a finite
commutative ring killed by `N`, and `N` is invertible on `T`. The equality `(N : Λ) = 0`
is equivalent to annihilation of every element by `N`, since `Λ` is a unital ring.
Invertibility on the scheme means that the constant global section `N` is a unit.
The sheaf and derived categories are precisely the imported ambient-foundation categories,
including `BoundedConstructibleDerivedCategory` for `Dᵇc`.
Source: blueprint `sec-smooth-base-change/sk-def-bc/sbc-def-coefficient-conventions.md`
(blueprint: sbc-def-coefficient-conventions). -/
def IsSmoothBaseChangeCoefficients (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    (T : Scheme.{u}) : Prop :=
  0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(T, ⊤))

end AlgebraicGeometry.Etale
