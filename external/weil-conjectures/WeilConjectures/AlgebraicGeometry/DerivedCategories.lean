/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Derived categories of etale sheaves of modules

Source: literature/blueprint/master/blueprint/sec-curve-estimates/
`lem-sc-second-kummer-divisors/def-weil-pbc-derived-categories.md`
(blueprint: def-weil-pbc-derived-categories); Stacks Project, Derived Categories, Tag 05RU.

The notions of the node are existing declarations, in the encoding of etale sheaves of
`Λ`-modules that the six-functor and proper-base-change chapters use
(`Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, `Λ : Type (u + 1)`):

* `D(T_et, Λ)` is `AlgebraicGeometry.Etale.DerivedCategoryModule Λ T`, i.e.
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`;
* `D(T_et)` is `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`;
* `H^i(K)` is `(DerivedCategory.homologyFunctor _ i).obj K`;
* `D^+(T_et, Λ)` and `D^b(T_et, Λ)` are `DerivedCategory.Plus` and `DerivedCategory.Bounded`
  of the same abelian category.

## Main definitions

* `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`: an object of `D(T_et, Λ)` has
  torsion cohomology. On `D^+` it restricts to the source's
  `AlgebraicGeometry.Etale.DerivedCategory.Plus.torsionHomology`
  (`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf`, stalkwise; the two
  agree by `AlgebraicGeometry.Scheme.isTorsionSheaf_iff_isTorsion`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- An object `K` of `D(T_et, Λ)` has *torsion cohomology* if every cohomology sheaf
`H^r(K)`, as a sheaf of abelian groups, is a torsion sheaf: every local section is locally
killed by a positive integer (`CategoryTheory.Sheaf.IsTorsion`).
Source: blueprint
`sec-curve-estimates/lem-sc-second-kummer-divisors/def-weil-pbc-derived-categories.md` (blueprint:
def-weil-pbc-derived-categories). -/
def DerivedCategory.torsionCohomology (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    ObjectProperty (DerivedCategoryModule Λ T) :=
  fun K ↦ ∀ r : ℤ, CategoryTheory.Sheaf.IsTorsion
    ((sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) r).obj K))

end AlgebraicGeometry.Etale
