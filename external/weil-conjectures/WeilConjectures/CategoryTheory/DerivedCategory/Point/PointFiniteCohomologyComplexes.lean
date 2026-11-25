/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # PointFiniteCohomologyComplexes

Source: Weil blueprint, `lemma-perfect-complexes-geometric-point`, order 1509
(blueprint: def-weil-point-finite-cohomology-complexes).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- The full-subcategory predicate: cohomology has finite support and the specified
finiteness property.
Source: blueprint order 1509 (blueprint: def-weil-point-finite-cohomology-complexes). -/
noncomputable def pointFiniteCohomology (R : Type u) [CommRing R] :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun K ↦ (∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) ∧
    (∀ i : ℤ, Finite ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K))

end DerivedCategory
