/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Nonempty intersections of simplex faces

Source: Stacks, Tag 0164, the category of finite nonempty ordered sets. The range
and intersection arguments below are agent-written consequences of this definition.
(auxiliary; not a blueprint node)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace SimplexCategory

/-- A simplex map factors through an injective map whenever its vertex range does.
Source: Stacks, Tag 0164 (finite ordered sets); agent-written proof. Take the unique
vertex preimages; injectivity reflects their order, so they form a monotone map.
The pointwise preimage equations give the result.
(auxiliary; not a blueprint node) -/
theorem factor_of_range_subset {a b c : SimplexCategory} (f : a ⟶ c) (e : b ⟶ c)
    [Mono e] (h : Set.range f.toOrderHom ⊆ Set.range e.toOrderHom) :
    ∃ g : a ⟶ b, g ≫ e = f := by
  classical
  have he : StrictMono e.toOrderHom :=
    e.toOrderHom.monotone.strictMono_of_injective (mono_iff_injective.mp inferInstance)
  have hx (x : Fin (a.len + 1)) : ∃ y, e.toOrderHom y = f.toOrderHom x := h ⟨x, rfl⟩
  choose g hg using hx
  refine ⟨Hom.mk ⟨g, ?_⟩, ?_⟩
  · intro x y hxy
    apply he.le_iff_le.mp
    rw [hg, hg]
    exact f.toOrderHom.monotone hxy
  · ext x
    exact congrArg Fin.val (hg x)

/-- Two injective simplex maps with a common vertex admit a pullback ordinal.
Source: Stacks, Tag 0164 (finite ordered sets); agent-written proof. Sort the vertices
of the first domain whose images lie in that of the second; this nonempty finite
ordered set is an ordinal. Its embedding
and the unique second preimages give the two projections. A compatible pair factors
through this sorted subset, and injectivity proves the second projection equation.
(auxiliary; not a blueprint node) -/
theorem exists_face_pullback {a b c : SimplexCategory} (e : a ⟶ c) (f : b ⟶ c)
    [Mono e] [Mono f]
    (hne : ∃ x y, e.toOrderHom x = f.toOrderHom y) :
    ∃ (p : SimplexCategory) (r : p ⟶ a) (s : p ⟶ b),
      Mono r ∧ Mono s ∧ r ≫ e = s ≫ f ∧
        ∀ (d : SimplexCategory) (q : d ⟶ a) (t : d ⟶ b), q ≫ e = t ≫ f →
          ∃ z : d ⟶ p, z ≫ r = q ∧ z ≫ s = t := by
  classical
  let S : Finset (Fin (a.len + 1)) := Finset.univ.filter
    (fun x ↦ ∃ y, e.toOrderHom x = f.toOrderHom y)
  have hS : S.Nonempty := by
    obtain ⟨x, y, hxy⟩ := hne
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hxy⟩⟩
  have hcard : S.card = (S.card - 1) + 1 := by
    have := Finset.card_pos.mpr hS
    omega
  let p : SimplexCategory := ⦋S.card - 1⦌
  let r : p ⟶ a := Hom.mk (S.orderEmbOfFin hcard).toOrderHom
  have hr : Mono r := (mono_iff_injective).mpr (S.orderEmbOfFin hcard).injective
  let := hr
  have hrange : Set.range (r ≫ e).toOrderHom ⊆ Set.range f.toOrderHom := by
    rintro _ ⟨x, rfl⟩
    have hx := S.orderEmbOfFin_mem hcard x
    obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hx).2
    exact ⟨y, hy.symm⟩
  obtain ⟨s, hs⟩ := factor_of_range_subset (r ≫ e) f hrange
  have hsmono : Mono s := by
    apply (mono_iff_injective).mpr
    intro x y hxy
    apply (mono_iff_injective.mp (inferInstance : Mono (r ≫ e)))
    have hval := congrArg (fun g : p ⟶ c ↦ g.toOrderHom x) hs
    have hval' := congrArg (fun g : p ⟶ c ↦ g.toOrderHom y) hs
    exact hval.symm.trans ((congrArg f.toOrderHom hxy).trans hval')
  refine ⟨p, r, s, hr, hsmono, hs.symm, ?_⟩
  intro d q t hqt
  have hqr : Set.range q.toOrderHom ⊆ Set.range r.toOrderHom := by
    rintro _ ⟨x, rfl⟩
    have hx : q.toOrderHom x ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, t.toOrderHom x, ?_⟩
      exact congrArg (fun g : d ⟶ c ↦ g.toOrderHom x) hqt
    exact (S.range_orderEmbOfFin hcard).symm ▸ hx
  obtain ⟨z, hz⟩ := factor_of_range_subset q r hqr
  refine ⟨z, hz, ?_⟩
  apply (cancel_mono f).mp
  rw [Category.assoc, hs, ← Category.assoc, hz, hqt]

end SimplexCategory
