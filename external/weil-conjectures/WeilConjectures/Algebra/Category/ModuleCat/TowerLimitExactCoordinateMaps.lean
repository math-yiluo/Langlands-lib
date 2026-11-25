/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Exact.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.TowerLimitInducedMaps

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- Dependent choice along `ℕ`: if some `x : X 0` satisfies `P 0`, and every `x : X n`
satisfying `P n` admits some `y : X (n + 1)` satisfying `P (n + 1)` and related to `x`
by `Q n`, then there is a whole sequence of such elements. -/
lemma Nat.exists_seq_of_exists_step {X : ℕ → Sort*} (P : ∀ n, X n → Prop)
    (Q : ∀ n, X (n + 1) → X n → Prop) (h₀ : ∃ x, P 0 x)
    (hstep : ∀ n x, P n x → ∃ y, P (n + 1) y ∧ Q n y x) :
    ∃ s : ∀ n, X n, ∀ n, P n (s n) ∧ Q n (s (n + 1)) (s n) := by
  let t : ∀ n, {x // P n x} := fun n ↦ Nat.rec ⟨h₀.choose, h₀.choose_spec⟩
    (fun n x ↦ ⟨(hstep n x.1 x.2).choose, (hstep n x.1 x.2).choose_spec.1⟩) n
  exact ⟨fun n ↦ (t n).1, fun n ↦ ⟨(t n).2, (hstep n _ (t n).2).choose_spec.2⟩⟩

namespace CategoryTheory

universe u v w t

/-- Coordinatewise exactness implies exactness of the induced maps on inverse limits;
with surjective kernel transitions the second induced map is surjective.
The levelwise maps `α` and `β` are required to commute with the transition maps
(hypotheses `hα` and `hβ`); without them the statement fails.
Source: Stacks Project, Algebra Lemma 03CA and Homology Lemma 02N1.
(blueprint: new-tower-limit-exact-coordinate-maps).
-/
theorem tower_limit_exact_of_coordinate_maps
    (R : Type u) [CommRing R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (G : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (H : ℕᵒᵖ ⥤ ModuleCat.{t} R)
    (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n))
    (β : ∀ n : ℕ, G.obj (Opposite.op n) →ₗ[R] H.obj (Opposite.op n))
    (hα : ∀ (n : ℕ) (x : F.obj (Opposite.op (n + 1))),
      G.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) x) =
        α n (F.map (homOfLE (Nat.le_add_right n 1)).op x))
    (hβ : ∀ (n : ℕ) (x : G.obj (Opposite.op (n + 1))),
      H.map (homOfLE (Nat.le_add_right n 1)).op (β (n + 1) x) =
        β n (G.map (homOfLE (Nat.le_add_right n 1)).op x))
    (hshort : ∀ n : ℕ, Function.Injective (α n) ∧ Function.Exact (α n) (β n) ∧
      Function.Surjective (β n))
    (U : ↑(limit F) →ₗ[R] ↑(limit G)) (V : ↑(limit G) →ₗ[R] ↑(limit H))
    (hU : ∀ (n : ℕ) (x : ↑(limit F)),
      limit.π G (Opposite.op n) (U x) = α n (limit.π F (Opposite.op n) x))
    (hV : ∀ (n : ℕ) (x : ↑(limit G)),
      limit.π H (Opposite.op n) (V x) = β n (limit.π G (Opposite.op n) x)) :
    Function.Injective U ∧ Function.Exact U V ∧
      ((∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_add_right n 1)).op)) →
        Function.Surjective V) := by
  refine ⟨?_, fun y ↦ ⟨fun hy ↦ ?_, ?_⟩, fun hF z ↦ ?_⟩
  · refine (injective_iff_map_eq_zero U).2 fun x hx ↦ Concrete.limit_ext _ _ _ ?_
    rintro ⟨n⟩
    refine (hshort n).1 ?_
    rw [← hU, hx, map_zero, map_zero, map_zero]
  · have h (n : ℕ) : ∃ x, α n x = limit.π G (Opposite.op n) y :=
      ((hshort n).2.1 _).1 (by rw [← hV, hy, map_zero])
    choose s hs using h
    refine ⟨towerLimitMk s fun n ↦ (hshort n).1 ?_, Concrete.limit_ext _ _ _ ?_⟩
    · rw [← hα, hs, hs]
      exact limit.w_apply G _ y
    · rintro ⟨n⟩
      rw [hU, limit_π_towerLimitMk, hs]
  · rintro ⟨x, rfl⟩
    refine Concrete.limit_ext _ _ _ ?_
    rintro ⟨n⟩
    rw [hV, hU, map_zero, ((hshort n).2.1 _).2 ⟨_, rfl⟩]
  · have hstep (n : ℕ) (y : G.obj (Opposite.op n)) (hy : β n y = limit.π H (Opposite.op n) z) :
        ∃ y' : G.obj (Opposite.op (n + 1)),
          β (n + 1) y' = limit.π H (Opposite.op (n + 1)) z ∧
            G.map (homOfLE (Nat.le_add_right n 1)).op y' = y := by
      obtain ⟨y₁, hy₁⟩ := (hshort (n + 1)).2.2 (limit.π H (Opposite.op (n + 1)) z)
      have hker : β n (G.map (homOfLE (Nat.le_add_right n 1)).op y₁ - y) = 0 := by
        rw [map_sub, ← hβ, hy₁, hy, limit.w_apply H, sub_self]
      obtain ⟨f, hf⟩ := ((hshort n).2.1 _).1 hker
      obtain ⟨f', rfl⟩ := hF n f
      refine ⟨y₁ - α (n + 1) f', ?_, ?_⟩
      · rw [map_sub, hy₁, ((hshort (n + 1)).2.1 _).2 ⟨_, rfl⟩, sub_zero]
      · rw [map_sub, hα, hf, sub_sub_cancel]
    obtain ⟨s, hs⟩ := Nat.exists_seq_of_exists_step _ _ ((hshort 0).2.2 _) hstep
    refine ⟨towerLimitMk s fun n ↦ (hs n).2, Concrete.limit_ext _ _ _ ?_⟩
    rintro ⟨n⟩
    rw [hV, limit_π_towerLimitMk, (hs n).1]

end CategoryTheory
