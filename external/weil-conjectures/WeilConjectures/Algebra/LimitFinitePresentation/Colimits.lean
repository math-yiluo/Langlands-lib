/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # The colimit of the models from their final pushout squares
Source: Stacks Tag 00R0, colimit clause, expanded using pushout universal properties.
(blueprint: lem-weil-pbc-limit-finite-presentation-colimits)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Algebra

/-- The final pushout squares transfer the base colimit to the model colimit.
Source: Stacks Tag 00R0, colimit clause (the non-local construction of Tag 00QV).
Proof: compose a cocone on `Sfun` with `η` and descend it through the base colimit.
At each index the pushout gives a map from `cS.pt` to the cocone point. For comparable
indices these maps agree by pushout uniqueness and cocone naturality. A common upper
bound then shows they agree at any two indices. Choose one index using nonemptiness;
its map factors every cocone leg. Uniqueness follows by pushout uniqueness at this index:
the `Sfun` leg is prescribed, and the base leg is prescribed by base-colimit uniqueness.
(blueprint: lem-weil-pbc-limit-finite-presentation-colimits)
-/
theorem colimits_of_limit_finite_presentation_core
    {Λ : Type u} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (fun a b => a ≤ b)]
    {Rfun Sfun : Λ ⥤ CommRingCat} (η : Rfun ⟶ Sfun)
    (cR : Cocone Rfun) (cS : Cocone Sfun) (φ : cR.pt ⟶ cS.pt)
    (hpush : ∀ l, Nonempty (CategoryTheory.IsPushout (η.app l) (cR.ι.app l) (cS.ι.app l) φ))
    (hcolR : IsColimit cR) : Nonempty (IsColimit cS) := by
  classical
  let p l := (hpush l).some
  let base (s : Cocone Sfun) : Cocone Rfun := ⟨s.pt, η ≫ s.ι⟩
  let d (s : Cocone Sfun) (l : Λ) : cS.pt ⟶ s.pt :=
    (p l).desc (s.ι.app l) (hcolR.desc (base s)) (by
      exact (hcolR.fac (base s) l).symm)
  have hdS (s : Cocone Sfun) (l : Λ) : cS.ι.app l ≫ d s l = s.ι.app l := by
    exact (p l).inl_desc _ _ _
  have hdR (s : Cocone Sfun) (l : Λ) : φ ≫ d s l = hcolR.desc (base s) := by
    exact (p l).inr_desc _ _ _
  have hdle (s : Cocone Sfun) (l m : Λ) (h : l ≤ m) : d s l = d s m := by
    apply (p l).hom_ext
    · rw [hdS, ← cS.w (homOfLE h), Category.assoc, hdS, s.w]
    · rw [hdR, hdR]
  have hdeq (s : Cocone Sfun) (l m : Λ) : d s l = d s m := by
    obtain ⟨k, hl, hm⟩ := IsDirected.directed (r := fun a b : Λ => a ≤ b) l m
    exact (hdle s l k hl).trans (hdle s m k hm).symm
  let l₀ : Λ := Classical.choice inferInstance
  refine ⟨{ desc := fun s => d s l₀, fac := ?_, uniq := ?_ }⟩
  · intro s l
    rw [← hdeq s l l₀, hdS]
  · intro s m hm
    apply (p l₀).hom_ext
    · rw [hm, hdS]
    · rw [hdR]
      apply hcolR.hom_ext
      intro l
      rw [← Category.assoc, ← (p l).w, Category.assoc, hm]
      exact (hcolR.fac (base s) l).symm

end Algebra
