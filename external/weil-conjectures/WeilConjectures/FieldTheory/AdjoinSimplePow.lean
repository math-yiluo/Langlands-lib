/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# Simple extensions and `p`-th powers

Auxiliary facts on simple field extensions in characteristic `p`:

- `IntermediateField.exists_mul_aeval_eq_aeval_of_mem_adjoin_simple`: an element of `k⟮x⟯` times a
  nonzero polynomial in `x` is a polynomial in `x`.
- `IntermediateField.pow_ne_of_mem_adjoin_simple`: if `x` is transcendental over `k`, then `x` is
  not a `p`-th power in `k⟮x⟯` for `p > 1`.
- `IsSeparable.mem_bot_of_pow_mem`: a separable element whose `q`-th power lies in the base field
  lies in the base field.
- `minpoly_eq_X_pow_sub_C_of_notMem_bot`: if `z ^ p = a` lies in the base field but `z` does not,
  then the minimal polynomial of `z` is `X ^ p - a`.
-/

@[expose] public section

open Polynomial IntermediateField

variable {k Q : Type*} [Field k] [Field Q] [Algebra k Q]

namespace IntermediateField

/-- An element of `k⟮x⟯` times a nonzero polynomial in `x` is a polynomial in `x`. -/
theorem exists_mul_aeval_eq_aeval_of_mem_adjoin_simple {x m : Q} (hm : m ∈ k⟮x⟯) :
    ∃ r s : k[X], aeval x s ≠ 0 ∧ m * aeval x s = aeval x r := by
  obtain ⟨r, s, rfl⟩ := (mem_adjoin_simple_iff k m).1 hm
  by_cases hs : aeval x s = 0
  · exact ⟨0, 1, by simp, by simp [hs]⟩
  · exact ⟨r, s, hs, div_mul_cancel₀ _ hs⟩

/-- A transcendental `x` is not an `n`-th power in `k⟮x⟯` for `n > 1`. -/
theorem pow_ne_of_mem_adjoin_simple {n : ℕ} (hn : 1 < n) {x y : Q} (hx : Transcendental k x)
    (hy : y ∈ k⟮x⟯) : y ^ n ≠ x := by
  intro h
  obtain ⟨r, s, hs, hrs⟩ := exists_mul_aeval_eq_aeval_of_mem_adjoin_simple hy
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (map_zero _)
  have hpoly : X * s ^ n = r ^ n := by
    refine sub_eq_zero.1 (transcendental_iff.1 hx _ ?_)
    rw [map_sub, map_mul, map_pow, map_pow, aeval_X, ← hrs, ← h]
    ring
  have hdeg := congrArg natDegree hpoly
  rw [natDegree_mul X_ne_zero (pow_ne_zero _ hs0), natDegree_X, natDegree_pow,
    natDegree_pow] at hdeg
  have hdvd : n ∣ 1 := (Nat.dvd_add_left (dvd_mul_right n _)).1 (hdeg ▸ dvd_mul_right n _)
  exact hn.ne' (Nat.dvd_one.1 hdvd)

end IntermediateField

/-- A separable element whose `q`-th power lies in the base field lies in the base field. -/
theorem IsSeparable.mem_bot_of_pow_mem {q : ℕ} [ExpChar k q] {a : Q} (ha : IsSeparable k a)
    (h : a ^ q ∈ (⊥ : IntermediateField k Q)) : a ∈ (⊥ : IntermediateField k Q) := by
  rwa [← adjoin_simple_eq_bot_iff, adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable k Q ha q,
    adjoin_simple_eq_bot_iff]

/-- If `z ^ p = a` lies in the base field but `z` does not, with `p` prime, then the minimal
polynomial of `z` is `X ^ p - a`. -/
theorem minpoly_eq_X_pow_sub_C_of_notMem_bot {p : ℕ} (hp : p.Prime) [CharP Q p] {z : Q} {a : k}
    (ha : algebraMap k Q a = z ^ p) (hz : z ∉ (⊥ : IntermediateField k Q)) :
    minpoly k z = X ^ p - C a := by
  refine (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hp fun b hb ↦ hz ?_)
    (by simp [ha]) (monic_X_pow_sub_C a hp.ne_zero)).symm
  have : Fact p.Prime := ⟨hp⟩
  refine mem_bot.2 ⟨b, frobenius_inj Q p ?_⟩
  rw [frobenius_def, frobenius_def, ← map_pow, hb, ha]
