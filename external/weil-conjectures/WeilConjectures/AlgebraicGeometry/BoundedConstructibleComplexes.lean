/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-!
# Bounded constructible complexes of etale sheaves of modules

Source: literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-p1/
`def-weil-pbc-constructible-complexes.md`
(blueprint: def-weil-pbc-constructible-complexes).

For a finite commutative ring `Λ` and a scheme `T`, `D^b_c(T_et, Λ)` is the full
subcategory of `D(T_et, Λ) = AlgebraicGeometry.Etale.DerivedCategoryModule Λ T` of the
complexes whose cohomology sheaves `H^i(K)` (`DerivedCategory.homologyFunctor`) are all
constructible (`AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`) and vanish
outside a bounded interval `[a, b]` of degrees.

The source's `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible` is not reused:
it is stated with the source's `Scheme.IsConstructibleSheaf` (finitely generated geometric
stalks), not with the project's recorded constructibility of
`def-weil-pbc-etale-constructible-sheaf` (finite constant module values).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- A complex `K ∈ D(T_et, Λ)`, `Λ` a finite commutative ring, is *bounded constructible* if
every cohomology sheaf `H^i(K)` is a constructible sheaf of `Λ`-modules
(`def-weil-pbc-etale-constructible-sheaf`) and there are integers `a ≤ b` with `H^i(K) = 0`
for `i ∉ [a, b]`.
Source: blueprint `sec-proper-base-change/sk-thm-p1/def-weil-pbc-constructible-complexes.md`
(blueprint: def-weil-pbc-constructible-complexes). -/
def DerivedCategory.isBoundedConstructible (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (T : Scheme.{u}) : ObjectProperty (DerivedCategoryModule Λ T) :=
  fun K ↦
    (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj K)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj K)

/-- `D^b_c(T_et, Λ) ⊂ D(T_et, Λ)`: the full subcategory of bounded constructible complexes.
Source: blueprint `sec-proper-base-change/sk-thm-p1/def-weil-pbc-constructible-complexes.md`
(blueprint: def-weil-pbc-constructible-complexes). -/
def BoundedConstructibleDerivedCategory (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (T : Scheme.{u}) : Type _ :=
  (DerivedCategory.isBoundedConstructible Λ T).FullSubcategory

noncomputable instance (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (T : Scheme.{u}) :
    Category (BoundedConstructibleDerivedCategory Λ T) :=
  inferInstanceAs (Category (DerivedCategory.isBoundedConstructible Λ T).FullSubcategory)

end AlgebraicGeometry.Etale
