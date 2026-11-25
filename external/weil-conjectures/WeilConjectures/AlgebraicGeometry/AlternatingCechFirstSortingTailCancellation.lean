/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import WeilConjectures.AlgebraicGeometry.AlternatingCechTailDeletionCorrespondence
import WeilConjectures.Combinatorics.SignedFacePermutation

/-!
# Tail deletions in the first sorting homotopy

Source: Stacks Project, Tag 01FM, equation 20.23.6.1, omitted verification.
(blueprint: lem-pc-alternating-cech-first-sorting-tail-cancellation)
-/

@[expose] public section

set_option autoImplicit false

universe v w

namespace AlgebraicGeometry.Scheme

private theorem sum_filtered {α : Type*} [Fintype α] {B : Type*} [AddCommMonoid B]
    (P : α → Prop) [DecidablePred P] (g : α → B) :
    (∑ x, if P x then g x else 0) = ∑ x : {x // P x}, g x.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) g

open Classical in
/-- The signed tail-deletion sum cancels exactly the incoming terms whose deleted
label does not precede the junction in stable order.

Source: Stacks 01FM, verification of equation 20.23.6.1, tail-deletion part
of the labelled-deletion argument (details omitted in the source).

Proof: Order labels j by (t j, j); the sorting filters then pick unique
permutations. In a filtered outgoing nonjunction term with a ≤ r, equality
r = a is impossible because the junction map takes a to σ a. Hence r > a.
Remove j = τ (r - 1), restrict the two permutations, and renumber remaining
labels increasingly. The prefix length stays b = a. The removed label is
outside the sorted prefix and differs from the junction, so it follows the
junction in the pair order. The restricted junction is exactly the outgoing
junction with entry r deleted, as a map to original labels. Conversely, for
an incoming label j following the junction, insert it in the stable sort at
its stable rank and in the partial sort's increasing tail at its original-label
rank. The induced outgoing deletion has r > a and removes a nonjunction
label. These constructions are inverse. The restricted permutation τ' has
sign τ' = (-1)^(r-1+j) sign τ, by moving the removed position r-1 and its
label j to the end before restricting. The incoming coefficient is therefore
(-1)^(j+a+r-1+j) sign τ, the negative of (-1)^(a+r) sign τ.
Sum along the bijection: each pair has the same f argument and opposite
integer coefficients. Distinct original labels make the pair order strict,
including when all values of t agree. The last prefix has no tail deletions
except the excluded junction occurrence; empty I has no input tuple.
(blueprint: lem-pc-alternating-cech-first-sorting-tail-cancellation) -/
theorem cechFirstSortingTailCancellation {I : Type v} [LinearOrder I] {B : Type w} [AddCommGroup B]
    (p : ℕ) (t : Fin (p + 2) → I) (f : (Fin (p + 2) → Fin (p + 2)) → B) :
    let before := fun (j : Fin (p + 2)) (σ : Equiv.Perm (Fin (p + 1)))
        (b : Fin (p + 1)) ↦
      t j < t (j.succAbove (σ b)) ∨
        (t j = t (j.succAbove (σ b)) ∧ j < j.succAbove (σ b))
    (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
      ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
        if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
            cechJunction σ τ a r ≠ σ a) ∧ ¬ r.val < a.val then
          (((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) * (-1 : ℤ) ^ r.val) •
            f (cechJunction σ τ a ∘ r.succAbove) else 0) +
      (∑ j : Fin (p + 2), ∑ σ : Equiv.Perm (Fin (p + 1)), ∑ b : Fin (p + 1),
        ∑ τ : Equiv.Perm (Fin (p + 1)),
          if (cechStableSort (t ∘ j.succAbove) σ ∧ cechPartialSort σ τ b) ∧
              ¬ before j σ b then
            ((-1 : ℤ) ^ j.val * ((-1 : ℤ) ^ b.val * (Equiv.Perm.sign τ : ℤ))) •
              f (j.succAbove ∘ cechJunction σ τ b) else 0) = 0 := by
  classical
  obtain ⟨e, he⟩ := cechTailDeletionCorrespondence p t
  let O := fun x : Equiv.Perm (Fin (p + 2)) × Fin (p + 2) ×
      Equiv.Perm (Fin (p + 2)) × Fin (p + 3) ↦
    (((-1 : ℤ) ^ x.2.1.val * (Equiv.Perm.sign x.2.2.1 : ℤ)) *
        (-1 : ℤ) ^ x.2.2.2.val) •
      f (cechJunction x.1 x.2.2.1 x.2.1 ∘ x.2.2.2.succAbove)
  let D := fun y : Fin (p + 2) × Equiv.Perm (Fin (p + 1)) × Fin (p + 1) ×
      Equiv.Perm (Fin (p + 1)) ↦
    ((-1 : ℤ) ^ y.1.val * ((-1 : ℤ) ^ y.2.2.1.val *
        (Equiv.Perm.sign y.2.2.2 : ℤ))) •
      f (y.1.succAbove ∘ cechJunction y.2.1 y.2.2.2 y.2.2.1)
  have hpair (x : cechTailOutgoingIndex p t) : O x.val + D (e x).val = 0 := by
    obtain ⟨k, hk, hj, hface, ha, hq⟩ := he x
    obtain ⟨η, hηface, hsign⟩ := Fin.signed_face_permutation (p + 1) x.val.2.2.1 k
    have hη : η = (e x).val.2.2.2 := by
      apply Equiv.ext
      intro z
      apply (Fin.succAbove_right_injective (p := (e x).val.1))
      rw [← hj, ← hηface z, hface z, hj]
    rw [hη, hj] at hsign
    have hcoeff :
        ((-1 : ℤ) ^ x.val.2.1.val * (Equiv.Perm.sign x.val.2.2.1 : ℤ)) *
            (-1 : ℤ) ^ x.val.2.2.2.val +
          (-1 : ℤ) ^ (e x).val.1.val * ((-1 : ℤ) ^ (e x).val.2.2.1.val *
            (Equiv.Perm.sign (e x).val.2.2.2 : ℤ)) = 0 := by
      rw [← hk, pow_succ, ha]
      calc
        _ = (-1 : ℤ) ^ (e x).val.2.2.1.val *
            (-(Equiv.Perm.sign x.val.2.2.1 : ℤ) * (-1 : ℤ) ^ k.val +
              (-1 : ℤ) ^ (e x).val.1.val *
                (Equiv.Perm.sign (e x).val.2.2.2 : ℤ)) := by ring
        _ = 0 := by rw [hsign]; ring
    dsimp only [O, D]
    rw [hq, ← add_smul, hcoeff, zero_smul]
  dsimp only
  simp only [← Fintype.sum_prod_type']
  rw [sum_filtered, sum_filtered]
  change (∑ x : cechTailOutgoingIndex p t, O x.val) +
    (∑ y : cechTailIncomingIndex p t, D y.val) = 0
  rw [← e.sum_comp (fun y ↦ D y.val), ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun x _ ↦ hpair x)

end AlgebraicGeometry.Scheme
