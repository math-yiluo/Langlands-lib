/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Explicit étale-origin witnesses

Source: Weil conjectures blueprint, proper base change,
`proposition-proper-direct-image-constructible-complexes--5`, order 1289
(blueprint: proposition-proper-direct-image-constructible-complexes--5).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- An explicit bounded-below étale origin for a pro-étale derived object.  The source
retains the étale complex and its comparison isomorphism as data, rather than merely
asserting that such data exists. Source: Weil conjectures blueprint,
`proposition-proper-direct-image-constructible-complexes--5` (blueprint:
proposition-proper-direct-image-constructible-complexes--5). -/
structure EtaleOriginWitness (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (K : FiniteCoefficientDerivedCategoryPlus T Λ) where
  /-- The bounded-below étale derived object furnishing the origin. -/
  L : DerivedCategory.Plus
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  /-- The specified comparison isomorphism from the étale origin to `K`. -/
  alpha : (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.obj L ≅ K

end AlgebraicGeometry.ProEtale
