/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import Mathlib.GroupTheory.Perm.Fin
import WeilConjectures.AlgebraicGeometry.AlternatingCechPrefixDeletionBijection

/-!
# Prefix deletions in the first sorting homotopy

Source: Stacks Project, Tag 01FM, equation 20.23.6.1, omitted verification.
(blueprint: lem-pc-alternating-cech-first-sorting-prefix-cancellation)
-/

@[expose] public section

set_option autoImplicit false

universe v w

namespace AlgebraicGeometry.Scheme

private theorem sign_restrict {n : ℕ} (τ : Equiv.Perm (Fin (n + 1)))
    (ρ : Equiv.Perm (Fin n)) (r j : Fin (n + 1)) (hj : τ r = j)
    (hρ : ∀ k, τ (r.succAbove k) = j.succAbove (ρ k)) :
    (Equiv.Perm.sign ρ : ℤ) =
      (-1 : ℤ) ^ j.val * (Equiv.Perm.sign τ : ℤ) * (-1 : ℤ) ^ r.val := by
  have he : j.cycleRange * τ * r.cycleRange⁻¹ =
      Equiv.Perm.decomposeFin.symm (0, ρ) := by
    ext k
    refine Fin.cases ?_ (fun k ↦ ?_) k
    · simp [Equiv.Perm.mul_apply, hj]
    · simp [Equiv.Perm.mul_apply, hρ]
  have hs := congrArg (fun e : Equiv.Perm (Fin (n + 1)) ↦
    (Equiv.Perm.sign e : ℤ)) he
  simpa using hs.symm

private theorem prefix_nonjunction {p : ℕ}
    (σ τ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2)) (r : Fin (p + 3))
    (hr : r.val < a.val) : cechJunction σ τ a r ≠ σ a := by
  intro h
  have hd : r.val ≤ a.val := le_of_lt hr
  have he : σ ⟨r.val, lt_trans hr a.isLt⟩ = σ a := by
    simpa only [cechJunction, dite_eq_left hd] using h
  have hv : r.val = a.val := congrArg Fin.val (σ.injective he)
  omega

private theorem prefix_filter {I : Type v} [LinearOrder I] {p : ℕ}
    (t : Fin (p + 2) → I) (σ τ : Equiv.Perm (Fin (p + 2)))
    (a : Fin (p + 2)) (r : Fin (p + 3)) :
    (((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
      cechJunction σ τ a r ≠ σ a) ∧ r.val < a.val) ↔
      ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧ r.val < a.val) := by
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, prefix_nonjunction σ τ a r h.2⟩, h.2⟩

private theorem junction_restrict (p : ℕ)
    (σ τ : Equiv.Perm (Fin (p + 2))) (ρ η : Equiv.Perm (Fin (p + 1)))
    (a : Fin (p + 2)) (b : Fin (p + 1)) (r j : Fin (p + 2))
    (ha : a.val = b.val + 1) (hr : r.val < a.val)
    (hσ : ∀ k, σ (r.succAbove k) = j.succAbove (ρ k))
    (hτ : ∀ k, τ (r.succAbove k) = j.succAbove (η k)) :
    cechJunction σ τ a ∘ r.castSucc.succAbove =
      j.succAbove ∘ cechJunction ρ η b := by
  funext k
  by_cases hk : k.val ≤ b.val
  · have hd : (r.castSucc.succAbove k).val ≤ a.val := by
      simp only [Fin.succAbove]
      split <;> simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;> omega
    simp only [Function.comp_apply, cechJunction, dite_eq_left hk, dite_eq_left hd]
    convert hσ ⟨k.val, by omega⟩ using 1
    congr 1
    apply Fin.ext
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split <;> simp_all only [Fin.val_castSucc, Fin.val_succ]
  · have hkr : ¬ k.castSucc < r.castSucc := by
      simp only [Fin.lt_def, Fin.val_castSucc]
      omega
    have hd : ¬ (r.castSucc.succAbove k).val ≤ a.val := by
      rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hkr)]
      simp only [Fin.val_succ]
      omega
    simp only [Function.comp_apply, cechJunction, dite_eq_right hk, dite_eq_right hd]
    convert hτ ⟨k.val - 1, by omega⟩ using 1
    congr 1
    apply Fin.ext
    change (r.castSucc.succAbove k).val - 1 = _
    rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hkr)]
    have hkr' : r ≤ (⟨k.val - 1, by omega⟩ : Fin (p + 1)).castSucc := by
      simp only [Fin.le_iff_val_le_val, Fin.val_castSucc]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hkr']
    simp only [Fin.val_succ]
    omega

private theorem sum_subtype_ite {α : Type*} [Fintype α] {B : Type*}
    [AddCommMonoid B] (P : α → Prop) [DecidablePred P] (g : α → B) :
    (∑ x, if P x then g x else 0) = ∑ x : {x // P x}, g x := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) g

open Classical in
/-- The signed prefix-deletion sum cancels exactly the incoming terms whose deleted
label precedes the junction in stable order.

Source: Stacks 01FM, verification of equation 20.23.6.1, prefix-deletion part
of the labelled-deletion argument (details omitted in the source).

Proof: Order labels j by the pairs (t j, j), so all labels are distinct even if
values repeat. The stable-sort filter has one permutation, and the partial-sort
filter has one permutation for each prefix length. For an outgoing term with
r < a, remove j = σ r = τ r. Restrict σ and τ to the other labels and renumber
those labels increasingly. The restricted stable sort is the stable sort of
the face omitting j; the restricted partial sort has prefix length b = a - 1.
The removed label precedes the remaining junction label in the pair order.
Deleting r from the outgoing junction gives exactly the incoming face junction,
as a map to the original labels. Conversely, insert the incoming deleted label
j at its stable rank r before the junction; set a = b + 1 and extend both
permutations. This inverts restriction, including at b = 0 and b = p.
If τ' is the restricted permutation, then sign τ' = (-1)^(r+j) sign τ:
move position r and label j to the end, then restrict, counting the two moves.
Thus the incoming coefficient is (-1)^(j+a-1+r+j) sign τ, the negative of
(-1)^(a+r) sign τ. Sum along this bijection. Each pair evaluates f on the
same map of labels and has opposite integer coefficients, so it cancels.
For a = 0 the outgoing prefix part is empty. Empty I has no input tuple.
(blueprint: lem-pc-alternating-cech-first-sorting-prefix-cancellation) -/
theorem cechFirstSortingPrefixCancellation
    {I : Type v} [LinearOrder I] {B : Type w} [AddCommGroup B]
    (p : ℕ) (t : Fin (p + 2) → I) (f : (Fin (p + 2) → Fin (p + 2)) → B) :
    let before := fun (j : Fin (p + 2)) (σ : Equiv.Perm (Fin (p + 1)))
        (b : Fin (p + 1)) ↦
      t j < t (j.succAbove (σ b)) ∨
        (t j = t (j.succAbove (σ b)) ∧ j < j.succAbove (σ b))
    (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
      ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
        if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
            cechJunction σ τ a r ≠ σ a) ∧ r.val < a.val then
          (((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) * (-1 : ℤ) ^ r.val) •
            f (cechJunction σ τ a ∘ r.succAbove) else 0) +
      (∑ j : Fin (p + 2), ∑ σ : Equiv.Perm (Fin (p + 1)), ∑ b : Fin (p + 1),
        ∑ τ : Equiv.Perm (Fin (p + 1)),
          if (cechStableSort (t ∘ j.succAbove) σ ∧ cechPartialSort σ τ b) ∧
              before j σ b then
            ((-1 : ℤ) ^ j.val * ((-1 : ℤ) ^ b.val * (Equiv.Perm.sign τ : ℤ))) •
              f (j.succAbove ∘ cechJunction σ τ b) else 0) = 0 := by
  classical
  dsimp only
  let O := CechPrefixOutgoing p t
  let N := CechPrefixIncoming p t
  let u : O → B := fun x ↦
    (((-1 : ℤ) ^ x.1.2.1.val * (Equiv.Perm.sign x.1.2.2.1 : ℤ)) *
      (-1 : ℤ) ^ x.1.2.2.2.val) •
      f (cechJunction x.1.1 x.1.2.2.1 x.1.2.1 ∘ x.1.2.2.2.succAbove)
  let z : N → B := fun y ↦
    ((-1 : ℤ) ^ y.1.1.val *
      ((-1 : ℤ) ^ y.1.2.2.1.val * (Equiv.Perm.sign y.1.2.2.2 : ℤ))) •
      f (y.1.1.succAbove ∘ cechJunction y.1.2.1 y.1.2.2.2 y.1.2.2.1)
  have hO :
      (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
        ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
          if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
              cechJunction σ τ a r ≠ σ a) ∧ r.val < a.val then
            (((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) * (-1 : ℤ) ^ r.val) •
              f (cechJunction σ τ a ∘ r.succAbove) else 0) = ∑ x, u x := by
    simp_rw [prefix_filter]
    simp only [← Fintype.sum_prod_type']
    exact sum_subtype_ite _ _
  have hN :
      (∑ j : Fin (p + 2), ∑ σ : Equiv.Perm (Fin (p + 1)), ∑ b : Fin (p + 1),
        ∑ τ : Equiv.Perm (Fin (p + 1)),
          if (cechStableSort (t ∘ j.succAbove) σ ∧ cechPartialSort σ τ b) ∧
              (t j < t (j.succAbove (σ b)) ∨
                (t j = t (j.succAbove (σ b)) ∧ j < j.succAbove (σ b))) then
            ((-1 : ℤ) ^ j.val * ((-1 : ℤ) ^ b.val * (Equiv.Perm.sign τ : ℤ))) •
              f (j.succAbove ∘ cechJunction σ τ b) else 0) = ∑ y, z y := by
    simp only [← Fintype.sum_prod_type']
    exact sum_subtype_ite _ _
  rw [hO, hN]
  obtain ⟨e, he⟩ := cechPrefixDeletionBijection p t
  have hterm : ∀ x : O, u x = -z (e x) := by
    intro x
    obtain ⟨ha, hr, hj, hσ, hτ⟩ := he x
    have hq := junction_restrict p x.1.1 x.1.2.2.1 (e x).1.2.1 (e x).1.2.2.2
      x.1.2.1 (e x).1.2.2.1 ⟨x.1.2.2.2.val, hr⟩ (e x).1.1 ha x.2.2 hσ hτ
    have hrEq : (⟨x.1.2.2.2.val, hr⟩ : Fin (p + 2)).castSucc = x.1.2.2.2 := rfl
    rw [hrEq] at hq
    have hs := sign_restrict x.1.2.2.1 (e x).1.2.2.2
      (⟨x.1.2.2.2.val, hr⟩ : Fin (p + 2)) (e x).1.1 hj hτ
    dsimp [u, z]
    rw [hq, hs]
    have hcoeff :
        ((-1 : ℤ) ^ x.1.2.1.val * (Equiv.Perm.sign x.1.2.2.1 : ℤ)) *
          (-1 : ℤ) ^ x.1.2.2.2.val =
        -((-1 : ℤ) ^ (e x).1.1.val *
          ((-1 : ℤ) ^ (e x).1.2.2.1.val *
            ((-1 : ℤ) ^ (e x).1.1.val * (Equiv.Perm.sign x.1.2.2.1 : ℤ) *
              (-1 : ℤ) ^ x.1.2.2.2.val))) := by
      rw [ha, pow_succ]
      have hj2 : (-1 : ℤ) ^ (e x).1.1.val * (-1 : ℤ) ^ (e x).1.1.val = 1 := by
        rw [← mul_pow]; norm_num
      linear_combination
        ((-1 : ℤ) ^ (e x).1.2.2.1.val * (Equiv.Perm.sign x.1.2.2.1 : ℤ) *
          (-1 : ℤ) ^ x.1.2.2.2.val) * hj2
    rw [hcoeff, neg_smul]
  rw [Fintype.sum_equiv e u (fun y ↦ -z y) hterm, Finset.sum_neg_distrib]
  exact neg_add_cancel _

end AlgebraicGeometry.Scheme
