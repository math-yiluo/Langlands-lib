/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-!
# The telescope presentation of an increasing union of submodules

Let `N 0 ≤ N 1 ≤ ⋯` be an increasing sequence of submodules of a module `M`. Let
`DirectSum.telescopeShift` be the endomorphism of `⨁ n, N n` sending the summand `N n` to the
summand `N (n + 1)` by the inclusion, and `DirectSum.telescopeSum : ⨁ n, N n →ₗ M` the sum
map. Then `0 ⟶ ⨁ n, N n ⟶ ⨁ n, N n ⟶ ⋃ n, N n ⟶ 0` is exact, the first map being
`id - telescopeShift`.

## Main statements

- `DirectSum.injective_id_sub_telescopeShift`
- `DirectSum.telescopeSum_comp_id_sub_telescopeShift`
- `DirectSum.ker_telescopeSum_le_range`
- `DirectSum.surjective_telescopeSum`
-/

@[expose] public section

namespace DirectSum

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (N : ℕ → Submodule R M)

/-- The shift endomorphism of `⨁ n, N n` for an increasing sequence of submodules `N`, mapping
the summand `N n` to the summand `N (n + 1)` by the inclusion. -/
noncomputable def telescopeShift (hN : Monotone N) : (⨁ n, N n) →ₗ[R] ⨁ n, N n :=
  toModule R ℕ _ fun n ↦ lof R ℕ (fun n ↦ N n) (n + 1) ∘ₗ Submodule.inclusion (hN n.le_succ)

/-- The sum map `⨁ n, N n →ₗ M` of a sequence of submodules. -/
noncomputable def telescopeSum : (⨁ n, N n) →ₗ[R] M :=
  toModule R ℕ M fun n ↦ (N n).subtype

variable {N}

@[simp]
lemma telescopeShift_lof (hN : Monotone N) (n : ℕ) (x : N n) :
    telescopeShift N hN (lof R ℕ (fun n ↦ N n) n x) =
      lof R ℕ (fun n ↦ N n) (n + 1) (Submodule.inclusion (hN n.le_succ) x) := by
  simp [telescopeShift]

@[simp]
lemma telescopeSum_lof (n : ℕ) (x : N n) :
    telescopeSum N (lof R ℕ (fun n ↦ N n) n x) = x := by
  simp [telescopeSum]

lemma telescopeSum_comp_id_sub_telescopeShift (hN : Monotone N) :
    telescopeSum N ∘ₗ (LinearMap.id - telescopeShift N hN) = 0 := by
  refine linearMap_ext _ fun n ↦ LinearMap.ext fun x ↦ ?_
  simp

/-- The partial sum map `x ↦ ∑_{n ≤ k} xₙ`. -/
private noncomputable def partialSum (N : ℕ → Submodule R M) (k : ℕ) :
    (⨁ n, N n) →ₗ[R] M :=
  toModule R ℕ M fun n ↦ if n ≤ k then (N n).subtype else 0

private lemma partialSum_id_sub_telescopeShift (hN : Monotone N) (k : ℕ) (x : ⨁ n, N n) :
    partialSum N k (x - telescopeShift N hN x) = (x k : M) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n y =>
    rw [← lof_eq_of R, map_sub, telescopeShift_lof]
    simp only [partialSum, toModule_lof]
    by_cases h : n = k
    · subst h
      simp [lof_eq_of]
    · rw [lof_eq_of, of_eq_of_ne _ _ _ (Ne.symm h)]
      rcases lt_or_gt_of_ne h with h' | h'
      · simp [h'.le, Nat.succ_le_of_lt h']
      · simp [not_le.2 h', not_le.2 (h'.trans (Nat.lt_succ_self n))]
  | add x y hx hy =>
    rw [map_add, add_sub_add_comm, map_add, hx, hy]
    simp

lemma injective_id_sub_telescopeShift (hN : Monotone N) :
    Function.Injective (LinearMap.id - telescopeShift N hN : (⨁ n, N n) →ₗ[R] ⨁ n, N n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  ext k
  have := partialSum_id_sub_telescopeShift hN k x
  simp only [LinearMap.sub_apply, LinearMap.id_apply] at hx
  rw [hx, map_zero] at this
  exact_mod_cast this.symm

private lemma lof_sub_lof_mem_range (hN : Monotone N) (n : ℕ) (y : N n) (m : ℕ)
    (hm : n ≤ m) :
    lof R ℕ (fun n ↦ N n) n y - lof R ℕ (fun n ↦ N n) m (Submodule.inclusion (hN hm) y) ∈
      LinearMap.range (LinearMap.id - telescopeShift N hN) := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨0, by rw [map_zero]; exact (sub_self _).symm⟩
  | succ m hm ih =>
    have := Submodule.add_mem _ ih
      (LinearMap.mem_range_self (LinearMap.id - telescopeShift N hN)
        (lof R ℕ (fun n ↦ N n) m (Submodule.inclusion (hN hm) y)))
    convert this using 1
    simp only [LinearMap.sub_apply, LinearMap.id_apply, telescopeShift_lof]
    abel_nf
    rfl

private lemma exists_sub_lof_mem_range (hN : Monotone N) (x : ⨁ n, N n) :
    ∃ (m : ℕ) (y : N m), x - lof R ℕ (fun n ↦ N n) m y ∈
      LinearMap.range (LinearMap.id - telescopeShift N hN) := by
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | of n y => exact ⟨n, y, by simp [lof_eq_of]⟩
  | add x₁ x₂ hx₁ hx₂ =>
    obtain ⟨m₁, y₁, h₁⟩ := hx₁
    obtain ⟨m₂, y₂, h₂⟩ := hx₂
    refine ⟨max m₁ m₂, Submodule.inclusion (hN (le_max_left m₁ m₂)) y₁ +
      Submodule.inclusion (hN (le_max_right m₁ m₂)) y₂, ?_⟩
    have := Submodule.add_mem _ (Submodule.add_mem _ h₁
      (lof_sub_lof_mem_range hN m₁ y₁ _ (le_max_left m₁ m₂)))
      (Submodule.add_mem _ h₂ (lof_sub_lof_mem_range hN m₂ y₂ _ (le_max_right m₁ m₂)))
    convert this using 1
    rw [map_add]
    abel

lemma ker_telescopeSum_le_range (hN : Monotone N) :
    LinearMap.ker (telescopeSum N) ≤ LinearMap.range (LinearMap.id - telescopeShift N hN) := by
  intro x hx
  obtain ⟨m, y, z, hz⟩ := exists_sub_lof_mem_range hN x
  have h₀ := congr(telescopeSum N $hz)
  rw [← LinearMap.comp_apply, telescopeSum_comp_id_sub_telescopeShift, LinearMap.zero_apply,
    map_sub, LinearMap.mem_ker.1 hx, telescopeSum_lof, zero_sub, eq_comm, neg_eq_zero,
    ZeroMemClass.coe_eq_zero] at h₀
  subst h₀
  rw [map_zero, sub_zero] at hz
  exact ⟨z, hz⟩

lemma surjective_telescopeSum (h : ∀ x : M, ∃ n, x ∈ N n) :
    Function.Surjective (telescopeSum N) := by
  intro x
  obtain ⟨n, hn⟩ := h x
  exact ⟨lof R ℕ (fun n ↦ N n) n ⟨x, hn⟩, by simp⟩

end DirectSum
