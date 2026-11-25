/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Option
/-!
# Signed permutations of deleted finite indices

Source: the signed-face calculation implicit in Stacks Project, Tag 01FG.
(blueprint: lem-pc-signed-face-permutation)
-/

@[expose] public section
set_option autoImplicit false

namespace Fin

/-- Deleting `k` from the domain and `σ k` from the range induces a permutation whose
sign compensates for the two deleted positions.
Source: Stacks 01FG, omitted verification of differential stability; Mathlib's
`Fin.cycleRange_succAbove`, `Fin.sign_cycleRange`, and `Equiv.optionCongr_sign`.

Proof: conjugate σ between the cycles moving k and σ(k) to zero. The resulting
permutation π fixes zero. Transport π to Option (Fin n) and remove its fixed none;
this constructs τ. The cycle identities show σ(k.succAbove a) = (σ k).succAbove (τ a).
Adding a fixed point and conjugating preserve sign, whereas the two cycles have signs
(-1)^k and (-1)^(σ k). Thus sign τ = (-1)^(σ k) sign σ (-1)^k. Multiplication by
(-1)^(σ k), whose square is one, gives the displayed identity. For n = 0 the face
condition is empty and both signs are one.
(blueprint: lem-pc-signed-face-permutation) -/
theorem signed_face_permutation (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    ∃ τ : Equiv.Perm (Fin n),
      (∀ a, σ (k.succAbove a) = (σ k).succAbove (τ a)) ∧
      (-1 : ℤ) ^ (σ k).val * (Equiv.Perm.sign τ : ℤ) =
        (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ k.val := by
  let π := (k.cycleRange.symm.trans σ).trans (σ k).cycleRange
  have hπ : π 0 = 0 := by simp [π]
  let ρ := (finSuccEquiv n).permCongr π
  have hρ : ρ none = none := by simp [ρ, Equiv.permCongr_def, hπ]
  let τ := Equiv.removeNone ρ
  have hτ : τ.optionCongr = ρ := by
    change (Equiv.removeNone ρ).optionCongr = ρ
    rw [map_equiv_removeNone, hρ, Equiv.swap_self]
    exact one_mul ρ
  refine ⟨τ, ?_, ?_⟩
  · intro a
    have h := congrArg (fun e : Equiv.Perm (Option (Fin n)) => e (some a)) hτ
    have hs : (τ a).succ = π a.succ := by
      apply (finSuccEquiv n).injective
      simpa [ρ, Equiv.permCongr_def] using h
    have h' := congrArg (σ k).cycleRange.symm hs
    simpa [π] using h'.symm
  · have hs : Equiv.Perm.sign τ = Equiv.Perm.sign π := by
      rw [← Equiv.optionCongr_sign τ, hτ, Equiv.Perm.sign_permCongr]
    have hs' : (Equiv.Perm.sign τ : ℤ) =
        (-1 : ℤ) ^ (σ k).val * (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ k.val := by
      rw [hs]
      simp [π, Equiv.Perm.sign_trans, Fin.sign_cycleRange, Equiv.Perm.sign_symm, mul_assoc]
    rw [hs']
    have hsq : (-1 : ℤ) ^ (σ k).val * (-1 : ℤ) ^ (σ k).val = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = ((-1 : ℤ) ^ (σ k).val * (-1 : ℤ) ^ (σ k).val) *
          ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ k.val) := by ring
      _ = _ := by rw [hsq, one_mul]

end Fin
