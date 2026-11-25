/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Filtered.Basic

/-! A filtered-colimit factorization condition for constant-model constructible sources.

Source: blueprint `lemma-continuity-ext-out-constructible-complex--1`, clause (1).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The degree-zero filtered-colimit factorization property needed for Ext from
constant-model constructible sheaves. This is a condition, not an assertion that
it holds on every scheme.
(blueprint: def-constant-model-ext-factorization). -/
def ConstantModelExtContinuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    IsConstantModelConstructible Λ X M →
    ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (F : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (c : Cocone F) (_hc : IsColimit c) (n : ℤ)
      (f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        ((DerivedCategory.singleFunctor _ 0).obj c.pt)⟦n⟧),
      ∃ (i : I) (g : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        ((DerivedCategory.singleFunctor _ 0).obj (F.obj i))⟦n⟧),
        f = g ≫ (shiftFunctor _ n).map ((DerivedCategory.singleFunctor _ 0).map (c.ι.app i))

end AlgebraicGeometry.ProEtale
