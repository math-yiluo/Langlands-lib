/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Compatibilities of the change of universe of `Ext`-groups

Mathlib's `CategoryTheory.Abelian.Ext.chgUniv` identifies `Ext.{w} X Y n` with `Ext.{w'} X Y n`
as types. We show that this bijection is additive and compatible with the composition of
`Ext`-groups and with `Ext.mk₀`.

## Main definitions

- `CategoryTheory.Abelian.Ext.chgUnivAddEquiv`: `Ext.chgUniv` as an additive equivalence.

## Main statements

- `CategoryTheory.Abelian.Ext.chgUniv_comp`: compatibility with composition.
- `CategoryTheory.Abelian.Ext.chgUniv_mk₀`: compatibility with `Ext.mk₀`.
-/

@[expose] public section

universe w'' w' w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasExt.{w'} C]
  {X Y Z : C}

lemma chgUniv_hom [HasDerivedCategory.{w''} C] {n : ℕ} (e : Ext.{w} X Y n) :
    (chgUniv.{w'} e).hom = e.hom :=
  homEquiv_chgUniv e

lemma chgUniv_add {n : ℕ} (a b : Ext.{w} X Y n) :
    chgUniv.{w'} (a + b) = chgUniv.{w'} a + chgUniv.{w'} b := by
  let := HasDerivedCategory.standard C
  ext
  simp only [chgUniv_hom, add_hom]

lemma chgUniv_comp {a b c : ℕ} (α : Ext.{w} X Y a) (β : Ext.{w} Y Z b) (h : a + b = c) :
    chgUniv.{w'} (α.comp β h) = (chgUniv.{w'} α).comp (chgUniv.{w'} β) h := by
  let := HasDerivedCategory.standard C
  ext
  simp only [chgUniv_hom, comp_hom]

lemma chgUniv_mk₀ (f : X ⟶ Y) : chgUniv.{w'} (mk₀.{w} f) = mk₀ f := by
  let := HasDerivedCategory.standard C
  ext
  simp only [chgUniv_hom, mk₀_hom]

variable (X Y) in
/-- The change of universe `Ext.{w} X Y n ≃ Ext.{w'} X Y n` as an additive equivalence. -/
noncomputable def chgUnivAddEquiv (n : ℕ) : Ext.{w} X Y n ≃+ Ext.{w'} X Y n where
  __ := chgUniv.{w'}
  map_add' := chgUniv_add

@[simp]
lemma chgUnivAddEquiv_apply {n : ℕ} (e : Ext.{w} X Y n) :
    chgUnivAddEquiv.{w', w} X Y n e = chgUniv.{w'} e :=
  rfl

end CategoryTheory.Abelian.Ext
