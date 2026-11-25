/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The change of coordinates of the top differential forms on projective space

Let `δ : R → N` satisfy the Leibniz rule (e.g. the universal derivation into Kähler
differentials). On the overlap of two standard charts `Uₚ`, `U_q` of projective space
`ℙᴰ` (homogeneous coordinates indexed by `Fin (D + 1)`), with affine coordinates
`y k = x_k / x_p` and `z k = x_k / x_q`, we have

`(-1)ᵖ ⋀_{k ≠ p} δ(y k) = (y q)^{D+1} • (-1)^q ⋀_{k ≠ q} δ(z k)`,

the wedge products being taken in increasing order of `k`. This is the computation behind
`ω_ℙ ≅ 𝒪(-D-1)` (blueprint: `theorem-riemann-roch-coherent-serre-duality--2`).

## Main statements

- `AlternatingMap.map_add_smul_self_of_eq_zero`: adding to every vector a multiple of a fixed
  vector `v m₀` does not change the value of an alternating map.
- `Fin.succAboveSwap`: the permutation of `Fin D` comparing the orders on `Fin (D + 1) \ {p}`
  and `Fin (D + 1) \ {q}` through the transposition of `p` and `q`, and its sign
  `Fin.sign_succAboveSwap`.
- `exteriorPower.ιMulti_chart_transition`: the change of coordinates formula above.
-/

@[expose] public section

open Equiv

namespace AlternatingMap

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Finite ι]

/-- Adding to every vector `v m` a multiple `d m • v m₀` of a fixed vector, with `d m₀ = 0`,
does not change the value of an alternating map. -/
theorem map_add_smul_self_of_eq_zero (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) (m₀ : ι) (d : ι → R)
    (hd : d m₀ = 0) : f (fun m ↦ v m + d m • v m₀) = f v := by
  classical
  let w (s : Finset ι) : ι → M := fun m ↦ if m ∈ s then v m + d m • v m₀ else v m
  have hw₀ (s : Finset ι) : w s m₀ = v m₀ := by
    simp only [w, hd, zero_smul, add_zero, ite_self]
  have key (s : Finset ι) : f (w s) = f v := by
    induction s using Finset.induction_on with
    | empty => simp [w]
    | insert a s ha ih =>
      by_cases ha₀ : a = m₀
      · subst ha₀
        have : w (insert a s) = w s := by
          funext m
          by_cases hm : m = a
          · subst hm
            rw [hw₀, hw₀]
          · simp [w, hm]
        rw [this, ih]
      · have : w (insert a s) = Function.update (w s) a (w s a + d a • w s m₀) := by
          funext m
          by_cases hm : m = a
          · subst hm
            simp [w, ha, hw₀]
          · simp [w, hm]
        have hz : f (Function.update (w s) a (w s m₀)) = 0 :=
          f.map_eq_zero_of_eq _ (i := a) (j := m₀)
            (by rw [Function.update_self, Function.update_of_ne (Ne.symm ha₀)]) ha₀
        rw [this, f.map_update_add, f.map_update_smul, hz, smul_zero, add_zero,
          Function.update_eq_self, ih]
  have := Fintype.ofFinite ι
  have h := key Finset.univ
  simp only [w, Finset.mem_univ] at h
  exact h

end AlternatingMap

namespace Fin

variable {D : ℕ} {p q : Fin (D + 1)}

/-- The permutation `τ` of `Fin D` with `q.succAbove (τ m) = swap p q (p.succAbove m)`: it compares
the increasing enumerations of `Fin (D + 1) \ {p}` and `Fin (D + 1) \ {q}` through the
transposition of `p` and `q`. -/
def succAboveSwap (p q : Fin (D + 1)) : Perm (Fin D) :=
  (finSuccAboveEquiv p).trans
    (((Equiv.swap p q).subtypeEquiv fun x ↦ by
      rw [ne_eq, ne_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]).trans
      (finSuccAboveEquiv q).symm)

lemma succAbove_succAboveSwap (m : Fin D) :
    q.succAbove (succAboveSwap p q m) = Equiv.swap p q (p.succAbove m) := by
  have h := (finSuccAboveEquiv q).apply_symm_apply
    ((Equiv.swap p q).subtypeEquiv (p := fun x ↦ x ≠ p) (q := fun x ↦ x ≠ q) (fun x ↦ by
      rw [ne_eq, ne_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right])
      (finSuccAboveEquiv p m))
  rw [finSuccAboveEquiv_apply] at h
  exact congrArg Subtype.val h

/-- **The sign of `succAboveSwap`**: `sign τ = -(-1)^p (-1)^q`. -/
lemma sign_succAboveSwap (hpq : p ≠ q) :
    Perm.sign (succAboveSwap p q) = -((-1) ^ (p : ℕ) * (-1) ^ (q : ℕ)) := by
  let P : Perm (Fin (D + 1)) := cycleRange q * Equiv.swap p q * (cycleRange p)⁻¹
  have hP : P = Perm.decomposeFin.symm (0, succAboveSwap p q) := by
    ext x
    induction x using Fin.cases with
    | zero =>
      rw [Perm.decomposeFin_symm_apply_zero]
      simp only [P, Perm.mul_apply, Perm.inv_def, cycleRange_symm_zero, swap_apply_left,
        cycleRange_self]
    | succ m =>
      rw [Perm.decomposeFin_symm_apply_succ, swap_self, refl_apply]
      simp only [P, Perm.mul_apply, Perm.inv_def, cycleRange_symm_succ]
      rw [← succAbove_succAboveSwap, cycleRange_succAbove]
  have h := congrArg Perm.sign hP
  rw [Perm.decomposeFin.symm_sign, ite_eq_left rfl, one_mul] at h
  rw [← h]
  simp only [P, map_mul, map_inv, sign_cycleRange, Perm.sign_swap hpq]
  rw [← inv_pow, inv_neg_one, mul_neg_one, neg_mul, mul_comm]

end Fin

namespace exteriorPower

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] {D : ℕ}

/-- **The change of coordinates of the top forms on projective space.** Let `δ : R → N` satisfy
the Leibniz rule, and let `y z : Fin (D + 1) → R` be the affine coordinates `y k = x_k / x_p` and
`z k = x_k / x_q` on the overlap of two standard charts, i.e. `y k = z k * y q` for `k ≠ p, q` and
`z p * y q = 1`. Then
`(-1)ᵖ ⋀_{k ≠ p} δ(y k) = (y q)^{D+1} (-1)^q ⋀_{k ≠ q} δ(z k)`. -/
theorem ιMulti_chart_transition (δ : R → N) (hδ : ∀ a b, δ (a * b) = a • δ b + b • δ a)
    (y z : Fin (D + 1) → R) {p q : Fin (D + 1)} (hpq : p ≠ q)
    (hy : ∀ k, k ≠ p → k ≠ q → y k = z k * y q) (hinv : z p * y q = 1) :
    ((-1) ^ (p : ℕ) : R) • ιMulti R D (fun m ↦ δ (y (p.succAbove m))) =
      (y q ^ (D + 1) * (-1) ^ (q : ℕ)) • ιMulti R D (fun m ↦ δ (z (q.succAbove m))) := by
  classical
  have hδ1 : δ 1 = 0 := by
    have h := hδ 1 1
    rw [mul_one, one_smul] at h
    simpa using h
  have hδq : δ (y q) = (-(y q * y q)) • δ (z p) := by
    have h := hδ (z p) (y q)
    rw [hinv, hδ1] at h
    calc δ (y q) = (y q * z p) • δ (y q) := by rw [mul_comm, hinv, one_smul]
      _ = (-(y q * y q)) • δ (z p) := by
        rw [neg_smul, eq_neg_iff_add_eq_zero, mul_smul, mul_smul, ← smul_add, ← h, smul_zero]
  obtain ⟨m₀, hm₀⟩ := Fin.exists_succAbove_eq hpq.symm
  let u (m : Fin D) : N := δ (z (q.succAbove m))
  let c (m : Fin D) : R := if m = m₀ then -(y q * y q) else y q
  let d (m : Fin D) : R := if m = m₀ then 0 else z (p.succAbove m)
  have hu (m : Fin D) : u (Fin.succAboveSwap p q m) = δ (z (swap p q (p.succAbove m))) := by
    simp only [u, Fin.succAbove_succAboveSwap]
  have hv : (fun m ↦ δ (y (p.succAbove m))) = fun m ↦
      c m • u (Fin.succAboveSwap p q m) + d m • (c m₀ • u (Fin.succAboveSwap p q m₀)) := by
    funext m
    by_cases hm : m = m₀
    · subst hm
      simp only [c, d, hu, hm₀, ite_true, zero_smul, add_zero, swap_apply_right, hδq]
    · have hk₁ : p.succAbove m ≠ p := Fin.succAbove_ne p m
      have hk₂ : p.succAbove m ≠ q := fun h ↦ hm (Fin.succAbove_right_injective (h.trans hm₀.symm))
      simp only [c, d, hm, hu, hm₀, ite_true, ite_false, swap_apply_of_ne_of_ne hk₁ hk₂,
        swap_apply_right, hy _ hk₁ hk₂, hδ, ← hδq]
      rw [add_comm]
  have hprod : ∏ m, c m = -(y q ^ (D + 1)) := by
    have hD : D - 1 + 2 = D + 1 := by
      have := m₀.pos
      omega
    rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ m₀),
      Finset.prod_congr rfl (fun m hm ↦ ite_eq_right (Finset.ne_of_mem_erase hm) : ∀ m ∈
        Finset.univ.erase m₀, c m = y q), Finset.prod_const, Finset.card_erase_of_mem
        (Finset.mem_univ m₀), Finset.card_univ, Fintype.card_fin, ← hD, pow_add]
    simp only [c, ite_true]
    ring
  have hsq : ((-1 : R) ^ (p : ℕ)) * (-1) ^ (p : ℕ) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [hv, AlternatingMap.map_add_smul_self_of_eq_zero (ιMulti R D)
      (fun m ↦ c m • u (Fin.succAboveSwap p q m)) m₀ d (by simp only [d, ite_true]),
    AlternatingMap.map_smul_univ]
  rw [show (fun m ↦ u (Fin.succAboveSwap p q m)) = u ∘ Fin.succAboveSwap p q from rfl,
    AlternatingMap.map_perm, Fin.sign_succAboveSwap hpq, hprod, Units.smul_def,
    ← Int.cast_smul_eq_zsmul R, smul_smul, smul_smul]
  congr 1
  push_cast
  linear_combination (y q ^ (D + 1) * (-1) ^ (q : ℕ)) * hsq

end exteriorPower
