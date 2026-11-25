/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.CharAndCard

/-!
# The unique finite subfield of an algebraic closure

Source: Weil conjectures blueprint, `chap-Nagata-compactification-and-Chows-lemma`,
`sk-prop-nagata-sketch-comp-category/def-weil-finite-field-fiber.md`, order 411
(blueprint: lem-weil-unique-subfield-of-closure).
-/

@[expose] public section

universe u v

namespace FiniteField

/-- The roots of `X ^ (q ^ n) - X` in an algebraic closure of a field with `q` elements
form its unique subfield with `q ^ n` elements. The image of the base field is the
root subfield for `n = 1`, is the unique subfield with `q` elements, and lies in every
such subfield. The final ring homomorphism is the corestriction of the base-field map;
via `RingHom.toAlgebra` it supplies the claimed base-field algebra structure.

Source: blueprint `def-weil-finite-field-fiber.md`, order 411
(blueprint: lem-weil-unique-subfield-of-closure).

Proof plan (Lang, Algebra, Ch. V, §5, Theorem 5.1, wanted but not obtained;
the six-step argument is recorded in the DAG):
1. The base field has characteristic `p`; its injective structure map gives the
   closure characteristic `p` too. Put `Q = q ^ n = p ^ (a * n)`; then `p ∣ Q` and `2 ≤ Q`.
2. The arithmetic Frobenius `FiniteField.frobeniusAlgEquivOfAlgebraic` and its `n`-th
   iterate fix precisely the roots of `X ^ Q - X`. Fixed points of a field automorphism
   form a subfield, containing the image of the base field.
3. Over the algebraically closed field, `Polynomial.Splits.eq_prod_roots` factors this
   monic degree-`Q` polynomial into linear factors. By `galois_poly_separable` its roots
   are simple, so there are exactly `Q` distinct roots.
4. For any subfield with `Q` elements, `FiniteField.pow_card` gives `x ^ Q = x`.
   It is therefore contained in the root subfield, and equal to it by finite cardinality.
5. The base-field image has `q` elements by injectivity. Apply uniqueness with `n = 1`
   to identify it with the roots of `X ^ q - X`. Such roots are also roots for every `n`
   by iterating the equation `x ^ q = x`.
6. Corestrict the structure map to the root subfield. Its composite with the inclusion
   is the original structure map, giving the asserted base-field algebra structure. -/
theorem exists_unique_subfield_of_closure
    (p a q : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hq : q = p ^ a)
    (k₀ : Type u) [Field k₀] [Finite k₀] (hcard : Nat.card k₀ = q)
    (k : Type v) [Field k] [Algebra k₀ k] [IsAlgClosure k₀ k]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ E : Subfield k,
      (∀ x : k, x ∈ E ↔ x ^ (q ^ n) = x) ∧
      Nat.card E = q ^ n ∧
      (∀ S : Subfield k, Nat.card S = q ^ n → S = E) ∧
      (algebraMap k₀ k).fieldRange ≤ E ∧
      (∀ x : k, x ∈ (algebraMap k₀ k).fieldRange ↔ x ^ q = x) ∧
      (∀ S : Subfield k, Nat.card S = q → S = (algebraMap k₀ k).fieldRange) ∧
      ∃ ι : k₀ →+* E, E.subtype.comp ι = algebraMap k₀ k := by
  classical
  let _ : Fintype k₀ := Fintype.ofFinite k₀
  have hc : Fintype.card k₀ = q := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hq2 : 1 < q := hc ▸ Fintype.one_lt_card
  have hqpos : 0 < q := lt_trans Nat.zero_lt_one hq2
  have _ : Fact p.Prime := ⟨hp⟩
  have _ : CharP k₀ p := charP_of_card_eq_prime_pow (hc.trans hq)
  have _ : IsAlgClosed k := IsAlgClosure.isAlgClosed k₀
  have _ : CharP k p := charP_of_injective_algebraMap' k₀ p
  let F (m : ℕ) : Subfield k :=
    ((frobeniusAlgEquivOfAlgebraic k₀ k ^ m).toRingHom).eqLocusField (RingHom.id k)
  have hmem (m : ℕ) (x : k) : x ∈ F m ↔ x ^ (q ^ m) = x := by
    change (frobeniusAlgEquivOfAlgebraic k₀ k ^ m) x = x ↔ _
    rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate, hc]
  have hcount (m : ℕ) (hm : 1 ≤ m) : Nat.card (F m) = q ^ m := by
    have hdegree : 1 < q ^ m := Nat.one_lt_pow (by omega) hq2
    have hne : (Polynomial.X ^ (q ^ m) - Polynomial.X : Polynomial k) ≠ 0 :=
      X_pow_card_sub_X_ne_zero k hdegree
    have hset : (F m : Set k) =
        (Polynomial.X ^ (q ^ m) - Polynomial.X : Polynomial k).rootSet k := by
      ext x
      change x ∈ F m ↔ _
      rw [hmem, Polynomial.mem_rootSet_of_ne hne]
      simp [sub_eq_zero]
    rw [← SetLike.coe_sort_coe, Nat.card_congr (Set.equivOfEq hset),
      Nat.card_eq_fintype_card]
    rw [Polynomial.card_rootSet_eq_natDegree
      (galois_poly_separable p (q ^ m) ?_) (IsAlgClosed.splits _)]
    · exact X_pow_card_sub_X_natDegree_eq k hdegree
    · rw [hq, ← pow_mul]
      exact dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))
  have hfinite (m : ℕ) (hm : 1 ≤ m) : Finite (F m) :=
    (Nat.card_pos_iff.mp (by rw [hcount m hm]; exact pow_pos hqpos m)).2
  have huniq (m : ℕ) (hm : 1 ≤ m) (S : Subfield k)
      (hS : Nat.card S = q ^ m) : S = F m := by
    have _ : Finite S :=
      (Nat.card_pos_iff.mp (by rw [hS]; exact pow_pos hqpos m)).2
    have _ : Finite (F m) := hfinite m hm
    let _ : Fintype S := Fintype.ofFinite S
    let _ : Fintype (F m) := Fintype.ofFinite (F m)
    have hle : S ≤ F m := by
      intro x hx
      apply (hmem m x).2
      have heq := congrArg S.subtype (pow_card (⟨x, hx⟩ : S))
      simpa only [map_pow, ← Nat.card_eq_fintype_card, hS, Subfield.subtype_apply] using heq
    apply SetLike.coe_injective
    apply Set.eq_of_subset_of_card_le hle
    simp only [← Nat.card_eq_fintype_card, SetLike.coe_sort_coe, hS, hcount m hm, le_refl]
  have hrange : Nat.card (algebraMap k₀ k).fieldRange = q :=
    (Nat.card_congr (algebraMap k₀ k).rangeRestrictFieldEquiv.toEquiv).symm.trans hcard
  have hrange_eq : (algebraMap k₀ k).fieldRange = F 1 :=
    huniq 1 (by omega) _ (by simpa using hrange)
  have hbase : (algebraMap k₀ k).fieldRange ≤ F n := by
    intro x hx
    obtain ⟨y, rfl⟩ := RingHom.mem_fieldRange.mp hx
    apply (hmem n _).2
    have heq := congrArg (algebraMap k₀ k) (pow_card_pow n y)
    simpa only [map_pow, hc] using heq
  refine ⟨F n, hmem n, hcount n hn, huniq n hn, hbase, ?_, ?_, ?_⟩
  · intro x
    rw [hrange_eq, hmem, pow_one]
  · intro S hS
    rw [hrange_eq]
    exact huniq 1 (by omega) S (by simpa using hS)
  · exact ⟨(algebraMap k₀ k).codRestrict (F n) (fun x ↦
      hbase (RingHom.mem_fieldRange_self _ x)), rfl⟩

end FiniteField
