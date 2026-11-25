/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Faithful exact functors reflect isomorphisms on derived categories

If `g : B ⥤ A` is a faithful exact functor between abelian categories, then the induced functor
`g.mapDerivedCategory` on derived categories reflects isomorphisms: a morphism of the derived
category is an isomorphism if and only if it induces isomorphisms on all homology objects, the
functor `g` commutes with homology (`Functor.mapDerivedCategoryHomologyFunctorIso`), and a faithful
exact functor between abelian categories reflects isomorphisms.
-/

@[expose] public section

open CategoryTheory Limits

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- The functor induced on derived categories by a faithful exact functor between abelian
categories reflects isomorphisms. -/
instance CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory_of_faithful (g : B ⥤ A)
    [g.Additive]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g] [g.Faithful] :
    g.mapDerivedCategory.ReflectsIsomorphisms where
  reflects {K L} φ h := by
    rw [DerivedCategory.isIso_iff]
    intro n
    rw [← isIso_iff_of_reflects_iso _ g, ← Functor.comp_map,
      NatIso.isIso_map_iff (g.mapDerivedCategoryHomologyFunctorIso n) φ, Functor.comp_map]
    infer_instance
