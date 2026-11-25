/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # Full faithfulness of bounded below etale realization -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Exact etale inverse image is full on bounded below complexes.
Source: Bhatt--Scholze, Corollary 5.1.6
(blueprint: lem-weil-pbc-finite-discrete-etale-realization-full).

Proof. The comparison derived adjunction has invertible unit on bounded below
complexes, so its hom map is bijective. Restrict the source along the fully faithful
inclusion of the bounded below derived category. -/
theorem finiteDiscreteEtaleRealization_full (B : Type) [CommRing B] (T : Scheme.{u}) :
    (DerivedCategory.Plus.ι ⋙
      D(ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)])).Full where
  map_surjective {K L} f := by
    obtain ⟨g, hg⟩ :=
      (bijective_comparisonUpperStar_mapDerivedCategory_map K.obj L.obj L.property).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩

end AlgebraicGeometry.ProEtale
