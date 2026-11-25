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
public import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! # PointFgCompleteComplexes

Source: Weil blueprint, `lemma-perfect-complexes-geometric-point`, order 1509
(blueprint: def-weil-point-fg-complete-complexes).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- The full-subcategory predicate: cohomology has finite support and the specified
finiteness property, and the object is derived complete for I.
Source: blueprint order 1509 (blueprint: def-weil-point-fg-complete-complexes). -/
noncomputable def pointFgComplete (R : Type u) [CommRing R] (I : Ideal R) :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun K ↦ (∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) ∧
    (∀ i : ℤ, Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) ∧
    DerivedCategory.IsDerivedComplete I K

end DerivedCategory
