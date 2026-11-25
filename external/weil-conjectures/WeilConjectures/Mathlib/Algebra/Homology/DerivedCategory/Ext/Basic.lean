/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Composition with an isomorphism on `Ext`-groups

## Main definitions

- `CategoryTheory.Abelian.Ext.precompAddEquiv`: an isomorphism `e : X ≅ X'` induces an
  isomorphism `Ext X' Z n ≃+ Ext X Z n` of `Ext`-groups by precomposition.
- `CategoryTheory.Abelian.Ext.postcompAddEquiv`: an isomorphism `e : Y ≅ Y'` induces an
  isomorphism `Ext X Y n ≃+ Ext X Y' n` of `Ext`-groups by postcomposition.

## Main statements

- `CategoryTheory.Abelian.Ext.subsingleton_sigma`: the `Ext`-groups out of a finite coproduct
  vanish if they vanish for each summand.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X X' : C}

/-- An isomorphism `e : X ≅ X'` induces an isomorphism `Ext X' Z n ≃+ Ext X Z n` of
`Ext`-groups by precomposition with `e`. -/
@[simps! apply]
noncomputable def precompAddEquiv (e : X ≅ X') (Z : C) (n : ℕ) : Ext X' Z n ≃+ Ext X Z n where
  __ := (Ext.mk₀ e.hom).precomp Z (zero_add n)
  invFun := (Ext.mk₀ e.inv).precomp Z (zero_add n)
  left_inv _ := by simp [Ext.mk₀_comp_mk₀_assoc]
  right_inv _ := by simp [Ext.mk₀_comp_mk₀_assoc]

/-- An isomorphism `e : Y ≅ Y'` induces an isomorphism `Ext X Y n ≃+ Ext X Y' n` of
`Ext`-groups by postcomposition with `e`. -/
@[simps! apply]
noncomputable def postcompAddEquiv (X : C) {Y Y' : C} (e : Y ≅ Y') (n : ℕ) :
    Ext X Y n ≃+ Ext X Y' n where
  __ := (Ext.mk₀ e.hom).postcomp X (add_zero n)
  invFun := (Ext.mk₀ e.inv).postcomp X (add_zero n)
  left_inv _ := by simp [Ext.mk₀_comp_mk₀]
  right_inv _ := by simp [Ext.mk₀_comp_mk₀]

open Limits in
/-- The `Ext`-groups out of a finite coproduct vanish if they vanish for each summand: `Ext`
commutes with finite biproducts in its first variable (`Ext.biproductAddEquiv`). -/
lemma subsingleton_sigma {ι : Type*} [Finite ι] (f : ι → C) [HasCoproduct f] (Z : C) (n : ℕ)
    [∀ j, Subsingleton (Ext (f j) Z n)] : Subsingleton (Ext (∐ f) Z n) := by
  -- reindex by `Fin k`, since the biproduct API is stated for index types in `Type`
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteCoproducts
  have (j : Fin k) : Subsingleton (Ext ((f ∘ e.symm) j) Z n) :=
    inferInstanceAs (Subsingleton (Ext (f (e.symm j)) Z n))
  have : Subsingleton (Ext (∐ (f ∘ e.symm)) Z n) :=
    ((precompAddEquiv (biproduct.isoCoproduct _) Z n).trans
      (biproductAddEquiv (biproduct.isBilimit _) Z n)).toEquiv.subsingleton
  exact (precompAddEquiv (Sigma.reindex e.symm f) Z n).toEquiv.subsingleton

end CategoryTheory.Abelian.Ext
