/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Order.CompletePartialOrder

/-!
# `lim¹` of a tower of finite abelian groups

A tower `⋯ → G₂ → G₁ → G₀` of finite abelian groups satisfies the Mittag-Leffler condition,
and its `lim¹`, the cokernel of `∏ₙ Gₙ → ∏ₙ Gₙ, (xₙ) ↦ (xₙ - φₙ(xₙ₊₁))`, vanishes (Stacks,
Tag 07KW). We prove the vanishing directly by Kőnig's lemma: for a fixed target `y`, the sets of
partial solutions `x₀, …, xₙ` of `xₖ - φₖ(xₖ₊₁) = yₖ` (`k < n`) form an inverse system of
nonempty finite sets, so it has a section.

## Main results

- `exists_sub_map_succ_eq_of_finite`: the map `(xₙ) ↦ (xₙ - φₙ(xₙ₊₁))` is surjective for a tower
  of finite abelian groups, that is, `lim¹ = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AddCommGroup

variable {G : ℕ → Type u} [∀ n, AddCommGroup (G n)] (φ : ∀ n, G (n + 1) →+ G n)
  (y : ∀ n, G n)

/-- The partial solutions of length `n` of the `lim¹` equation `xₖ - φₖ(xₖ₊₁) = yₖ`: the
sequences satisfying the equation for `k < n` and vanishing beyond `n`. -/
def TowerPartialSolution (n : ℕ) : Type u :=
  {x : ∀ k, G k // (∀ k < n, x k - φ k (x (k + 1)) = y k) ∧ ∀ k, n < k → x k = 0}

/-- The truncation of a sequence after the index `n`. -/
def towerTruncate (n : ℕ) (x : ∀ k, G k) : ∀ k, G k :=
  fun k ↦ if k ≤ n then x k else 0

/-- The truncation of a partial solution of length `m` to one of length `n ≤ m`. -/
def TowerPartialSolution.truncate {n m : ℕ} (h : n ≤ m) (x : TowerPartialSolution φ y m) :
    TowerPartialSolution φ y n :=
  ⟨towerTruncate n x.1, fun k hk ↦ by
    simp only [towerTruncate, ite_eq_left hk.le, ite_eq_left (Nat.succ_le_of_lt hk)]
    exact x.2.1 k (lt_of_lt_of_le hk h), fun k hk ↦ by
    simp only [towerTruncate, ite_eq_right (not_le.2 hk)]⟩

/-- The inverse system of the partial solutions of the `lim¹` equation. -/
def towerPartialSolutions : ℕᵒᵖ ⥤ Type u where
  obj n := TowerPartialSolution φ y n.unop
  map f := TypeCat.ofHom fun x ↦ x.truncate φ y (leOfHom f.unop)
  map_id n := by
    ext x
    refine Subtype.ext (funext fun k ↦ ?_)
    change (if k ≤ n.unop then x.1 k else 0) = x.1 k
    split_ifs with hk
    · rfl
    · exact (x.2.2 k (not_le.1 hk)).symm
  map_comp f g := by
    ext x
    refine Subtype.ext (funext fun k ↦ ?_)
    change (if k ≤ _ then x.1 k else 0) =
      if k ≤ _ then (if k ≤ _ then x.1 k else 0) else 0
    have h₁ := leOfHom f.unop
    have h₂ := leOfHom g.unop
    split_ifs <;> first | rfl | omega

/-- The solution of the `lim¹` equation obtained by solving it downwards from `x_d = 0`: the
term of index `k` of the solution of length `k + d`. -/
def towerDownwardSolution : ℕ → ∀ k, G k
  | 0 => fun _ ↦ 0
  | d + 1 => fun k ↦ y k + φ k (towerDownwardSolution d (k + 1))

instance (n : ℕ) : Nonempty (TowerPartialSolution φ y n) := by
  refine ⟨⟨fun k ↦ towerDownwardSolution φ y (n - k) k, fun k hk ↦ ?_, fun k hk ↦ ?_⟩⟩
  · obtain ⟨d, hd⟩ : ∃ d, n - k = d + 1 := ⟨n - k - 1, by omega⟩
    have hd' : n - (k + 1) = d := by omega
    dsimp only
    rw [hd, hd', towerDownwardSolution, add_sub_cancel_right]
  · dsimp only
    rw [show n - k = 0 by omega]
    rfl

instance [∀ n, Finite (G n)] (n : ℕ) : Finite (TowerPartialSolution φ y n) :=
  Finite.of_injective (fun x (k : Fin (n + 1)) ↦ x.1 k) fun x x' h ↦ by
    refine Subtype.ext (funext fun k ↦ ?_)
    by_cases hk : k ≤ n
    · exact congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
    · rw [x.2.2 k (not_le.1 hk), x'.2.2 k (not_le.1 hk)]

/-- *Mittag-Leffler vanishing*: for a tower `φₙ : Gₙ₊₁ → Gₙ` of finite abelian groups the map
`∏ₙ Gₙ → ∏ₙ Gₙ, (xₙ) ↦ (xₙ - φₙ(xₙ₊₁))` is surjective, that is, `lim¹ Gₙ = 0`. The partial
solutions form an inverse system of nonempty finite sets, which has a section by Kőnig's lemma
(`nonempty_sections_of_finite_inverse_system`).
(blueprint: `lem-weil-pbc-mittag-leffler`) -/
theorem exists_sub_map_succ_eq_of_finite [∀ n, Finite (G n)] :
    ∃ x : ∀ n, G n, ∀ n, x n - φ n (x (n + 1)) = y n := by
  have : ∀ n : ℕᵒᵖ, Finite ((towerPartialSolutions φ y).obj n) := fun n ↦
    inferInstanceAs (Finite (TowerPartialSolution φ y n.unop))
  have : ∀ n : ℕᵒᵖ, Nonempty ((towerPartialSolutions φ y).obj n) := fun n ↦
    inferInstanceAs (Nonempty (TowerPartialSolution φ y n.unop))
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system (towerPartialSolutions φ y)
  refine ⟨fun k ↦ (s (op k)).1 k, fun k ↦ ?_⟩
  have h := congrArg (fun x : TowerPartialSolution φ y k ↦ x.1 k)
    (hs (homOfLE k.le_succ).op)
  change (if k ≤ k then (s (op (k + 1))).1 k else 0) = (s (op k)).1 k at h
  rw [ite_eq_left le_rfl] at h
  dsimp only
  rw [← h]
  exact (s (op (k + 1))).2.1 k k.lt_succ_self

end AddCommGroup
