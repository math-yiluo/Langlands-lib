/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SimplicialOrdinalPath
import WeilConjectures.CategoryTheory.SimplexMonoPullback
import Mathlib.Tactic

/-!
# Intersections of faces in the ordered path simplex

Source: Stacks, Tags 017J and 01GN: compatible maps on the finite union of the two
endpoints and doubled proper faces glue before finite-simplex lifting is applied.
(auxiliary; not a blueprint node)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace SimplexCategory.OrdinalPath

lemma vertex_cases {n : SimplexCategory} (j : Fin ((obj n).len + 1)) :
    (∃ i, j = (left n).toOrderHom i) ∨ (∃ i, j = (right n).toOrderHom i) := by
  by_cases h : j.val ≤ n.len
  · exact Or.inl ⟨⟨j.val, by omega⟩, rfl⟩
  · refine Or.inr ⟨⟨j.val - (n.len + 1), ?_⟩, ?_⟩
    · have := j.isLt
      dsimp [obj] at this
      omega
    · apply Fin.ext
      dsimp [right]
      omega

@[simp]
lemma map_left_vertex {a b : SimplexCategory} (f : a ⟶ b) (i : Fin (a.len + 1)) :
    (map f).toOrderHom ((left a).toOrderHom i) = (left b).toOrderHom (f.toOrderHom i) :=
  map_apply_left f i

@[simp]
lemma map_right_vertex {a b : SimplexCategory} (f : a ⟶ b) (i : Fin (a.len + 1)) :
    (map f).toOrderHom ((right a).toOrderHom i) = (right b).toOrderHom (f.toOrderHom i) :=
  map_apply_right f i

lemma left_right_ne {a : SimplexCategory} (i j : Fin (a.len + 1)) :
    (left a).toOrderHom i ≠ (right a).toOrderHom j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  dsimp [left, right] at hv
  omega

instance map_mono {a b : SimplexCategory} (f : a ⟶ b) [Mono f] : Mono (map f) := by
  apply mono_iff_injective.mpr
  intro i j hij
  rcases vertex_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases vertex_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [map_left_vertex] at hij
    have hv := congrArg (fun z : Fin ((obj b).len + 1) ↦ z.val) hij
    have he : f.toOrderHom i = f.toOrderHom j := Fin.ext hv
    exact congrArg (left a).toOrderHom ((mono_iff_injective.mp inferInstance) he)
  · simp only [map_left_vertex, map_right_vertex] at hij
    exact False.elim (left_right_ne _ _ hij)
  · simp only [map_left_vertex, map_right_vertex] at hij
    exact False.elim (left_right_ne _ _ hij.symm)
  · simp only [map_right_vertex] at hij
    have he : f.toOrderHom i = f.toOrderHom j := by
      apply Fin.ext
      have hv := congrArg Fin.val hij
      dsimp [right] at hv
      omega
    exact congrArg (right a).toOrderHom ((mono_iff_injective.mp inferInstance) he)

instance left_mono (a : SimplexCategory) : Mono (left a) := by
  apply mono_iff_injective.mpr
  intro i j hij
  have hv := congrArg (fun z : Fin ((obj a).len + 1) ↦ z.val) hij
  exact Fin.ext hv

instance right_mono (a : SimplexCategory) : Mono (right a) := by
  apply mono_iff_injective.mpr
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  dsimp [right] at hv
  omega

/-- The intersection of a first endpoint with a doubled face is its first endpoint. -/
theorem left_face_factor {a c d : SimplexCategory} (f : a ⟶ c)
    (q : d ⟶ c) (t : d ⟶ obj a) (h : q ≫ left c = t ≫ map f) :
    ∃ r : d ⟶ a, q = r ≫ f ∧ t = r ≫ left a := by
  have htr : Set.range t.toOrderHom ⊆ Set.range (left a).toOrderHom := by
    rintro _ ⟨i, rfl⟩
    rcases vertex_cases (t.toOrderHom i) with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨x, hx.symm⟩
    · have hi := congrArg (fun g : d ⟶ obj c ↦ g.toOrderHom i) h
      change (left c).toOrderHom (q.toOrderHom i) = (map f).toOrderHom (t.toOrderHom i)
        at hi
      rw [hx, map_right_vertex] at hi
      exact False.elim (left_right_ne _ _ hi)
  obtain ⟨r, hr⟩ := factor_of_range_subset t (left a) htr
  refine ⟨r, ?_, hr.symm⟩
  apply (cancel_mono (left c)).mp
  rw [h, ← hr, Category.assoc, left_naturality, ← Category.assoc]

/-- The intersection of a second endpoint with a doubled face is its second endpoint. -/
theorem right_face_factor {a c d : SimplexCategory} (f : a ⟶ c)
    (q : d ⟶ c) (t : d ⟶ obj a) (h : q ≫ right c = t ≫ map f) :
    ∃ r : d ⟶ a, q = r ≫ f ∧ t = r ≫ right a := by
  have htr : Set.range t.toOrderHom ⊆ Set.range (right a).toOrderHom := by
    rintro _ ⟨i, rfl⟩
    rcases vertex_cases (t.toOrderHom i) with ⟨x, hx⟩ | ⟨x, hx⟩
    · have hi := congrArg (fun g : d ⟶ obj c ↦ g.toOrderHom i) h
      change (right c).toOrderHom (q.toOrderHom i) = (map f).toOrderHom (t.toOrderHom i)
        at hi
      rw [hx, map_left_vertex] at hi
      exact False.elim (left_right_ne _ _ hi.symm)
    · exact ⟨x, hx.symm⟩
  obtain ⟨r, hr⟩ := factor_of_range_subset t (right a) htr
  refine ⟨r, ?_, hr.symm⟩
  apply (cancel_mono (right c)).mp
  rw [h, ← hr, Category.assoc, right_naturality, ← Category.assoc]

/-- Equality under doubled maps identifies the block and the underlying images. -/
lemma map_eq_blocks {a b c : SimplexCategory} (e : a ⟶ c) (f : b ⟶ c)
    (i : Fin ((obj a).len + 1)) (j : Fin ((obj b).len + 1))
    (h : (map e).toOrderHom i = (map f).toOrderHom j) :
    (∃ x y, i = (left a).toOrderHom x ∧ j = (left b).toOrderHom y ∧
      e.toOrderHom x = f.toOrderHom y) ∨
    (∃ x y, i = (right a).toOrderHom x ∧ j = (right b).toOrderHom y ∧
      e.toOrderHom x = f.toOrderHom y) := by
  rcases vertex_cases i with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases vertex_cases j with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · simp only [map_left_vertex] at h
    have hv := congrArg (fun z : Fin ((obj c).len + 1) ↦ z.val) h
    exact Or.inl ⟨x, y, rfl, rfl, Fin.ext hv⟩
  · simp only [map_left_vertex, map_right_vertex] at h
    exact False.elim (left_right_ne _ _ h)
  · simp only [map_left_vertex, map_right_vertex] at h
    exact False.elim (left_right_ne _ _ h.symm)
  · simp only [map_right_vertex] at h
    refine Or.inr ⟨x, y, rfl, rfl, ?_⟩
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [right] at hv
    omega

/-- Doubling preserves the nonempty intersection of two injective faces. -/
theorem doubled_face_intersection {a b c d : SimplexCategory}
    (e : a ⟶ c) (f : b ⟶ c) [Mono e] [Mono f]
    (q : d ⟶ obj a) (t : d ⟶ obj b) (hqt : q ≫ map e = t ≫ map f) :
    ∃ (p : SimplexCategory) (r : p ⟶ a) (s : p ⟶ b) (z : d ⟶ obj p),
      Mono r ∧ Mono s ∧ r ≫ e = s ≫ f ∧ z ≫ map r = q ∧ z ≫ map s = t := by
  have hpoint (i : Fin (d.len + 1)) :=
    congrArg (fun g : d ⟶ obj c ↦ g.toOrderHom i) hqt
  have hne : ∃ x y, e.toOrderHom x = f.toOrderHom y := by
    rcases map_eq_blocks e f _ _ (hpoint 0) with ⟨x, y, _, _, hxy⟩ | ⟨x, y, _, _, hxy⟩ <;>
      exact ⟨x, y, hxy⟩
  obtain ⟨p, r, s, hr, hs, hrs, huniv⟩ := exists_face_pullback e f hne
  let := hr
  let := hs
  have hbase (x : Fin (a.len + 1)) (y : Fin (b.len + 1))
      (hxy : e.toOrderHom x = f.toOrderHom y) :
      ∃ z, r.toOrderHom z = x ∧ s.toOrderHom z = y := by
    let q₀ : ⦋0⦌ ⟶ a := Hom.mk ⟨fun _ ↦ x, fun _ _ _ ↦ le_rfl⟩
    let t₀ : ⦋0⦌ ⟶ b := Hom.mk ⟨fun _ ↦ y, fun _ _ _ ↦ le_rfl⟩
    have heq : q₀ ≫ e = t₀ ≫ f := by ext i; exact congrArg Fin.val hxy
    obtain ⟨z, hz, hz'⟩ := huniv ⦋0⦌ q₀ t₀ heq
    exact ⟨z.toOrderHom 0, congrArg (fun g : ⦋0⦌ ⟶ a ↦ g.toOrderHom 0) hz,
      congrArg (fun g : ⦋0⦌ ⟶ b ↦ g.toOrderHom 0) hz'⟩
  have hqr : Set.range q.toOrderHom ⊆ Set.range (map r).toOrderHom := by
    rintro _ ⟨i, rfl⟩
    rcases map_eq_blocks e f _ _ (hpoint i) with ⟨x, y, hx, _, hxy⟩ | ⟨x, y, hx, _, hxy⟩
    · obtain ⟨z, hz, _⟩ := hbase x y hxy
      exact ⟨(left p).toOrderHom z, by rw [map_left_vertex, hz, hx]⟩
    · obtain ⟨z, hz, _⟩ := hbase x y hxy
      exact ⟨(right p).toOrderHom z, by rw [map_right_vertex, hz, hx]⟩
  obtain ⟨z, hz⟩ := factor_of_range_subset q (map r) hqr
  refine ⟨p, r, s, z, hr, hs, hrs, hz, ?_⟩
  apply (cancel_mono (map f)).mp
  have hmap : map s ≫ map f = map r ≫ map e := by
    change doubling.map s ≫ doubling.map f = doubling.map r ≫ doubling.map e
    rw [← doubling.map_comp, ← hrs, doubling.map_comp]
  rw [Category.assoc, hmap, ← Category.assoc, hz, hqt]

end SimplexCategory.OrdinalPath
