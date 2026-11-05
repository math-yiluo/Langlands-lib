import Mathlib

/-!
# Homogeneous symmetric polynomial 2-cocycles

Coefficient-level core of the polynomial cocycle lemma.
-/

namespace Langlands.Algebra.PolynomialCocycle

open Finset

variable {k : Type*} [Field k]

/-- The power sum `∑_{i < p} i ^ j` computed in `k`. -/
def powerSum (k : Type*) [Field k] (p j : ℕ) : k := ∑ i ∈ range p, (i : k) ^ j

/-- Coefficient conditions on `d` for the homogeneous polynomial
`c = ∑_{i ≤ n} d i x^i y^(n-i)` to be a symmetric 2-cocycle with `c(0, y) = 0`. -/
structure IsHomCocycle (n : ℕ) (d : ℕ → k) : Prop where
  zero : d 0 = 0
  top : d n = 0
  symm : ∀ i ≤ n, d i = d (n - i)
  coc : ∀ a b, 0 < a → 0 < b → a + b < n →
    d (a + b) * ((a + b).choose a : k) = d a * ((n - a).choose b : k)

namespace IsHomCocycle

variable {n : ℕ} {d : ℕ → k}

/-- The relation obtained from the cocycle condition with first index `1`. -/
theorem mul_eq (h : IsHomCocycle n d) {j : ℕ} (hj : 0 < j) (hjn : j < n) :
    (j : k) * d j = d 1 * ((n - 1).choose (j - 1) : k) := by
  rcases Nat.lt_or_ge 1 j with h1 | h1
  · have := h.coc 1 (j - 1) one_pos (by omega) (by omega)
    rw [show 1 + (j - 1) = j by omega, Nat.choose_one_right] at this
    rw [mul_comm, this]
  · obtain rfl : j = 1 := by omega
    simp

/-- In the boundary of degree `n`, `j * C(n, j) = n * C(n - 1, j - 1)`. -/
theorem cast_mul_choose {n j : ℕ} (hj : 0 < j) (hn : 0 < n) :
    (j : k) * (n.choose j : k) = (n : k) * ((n - 1).choose (j - 1) : k) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hN : (j + 1) * (n + 1).choose (j + 1) = (n + 1) * n.choose j := by
    rw [Nat.add_one_mul_choose_eq n j]; ring
  simp only [Nat.add_sub_cancel]
  rw [← Nat.cast_mul, ← Nat.cast_mul, hN]

end IsHomCocycle

section CharZero

variable [CharZero k]

/-- In characteristic zero every homogeneous symmetric 2-cocycle is a coboundary. -/
theorem IsHomCocycle.exists_eq_charZero {n : ℕ} {d : ℕ → k} (h : IsHomCocycle n d) :
    ∃ g : k, ∀ i, 0 < i → i < n → d i = g * (n.choose i : k) := by
  refine ⟨d 1 / n, fun i hi hin => ?_⟩
  have hn : (n : k) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hi' : (i : k) ≠ 0 := by exact_mod_cast hi.ne'
  apply mul_left_cancel₀ hi'
  rw [h.mul_eq hi hin, ← mul_assoc, mul_comm (i : k), mul_assoc,
    IsHomCocycle.cast_mul_choose hi (by omega)]
  field_simp

end CharZero

section CharP

variable (p : ℕ) [hp : Fact p.Prime] [CharP k p]

include hp in
/-- Lucas' theorem for multiples of `p`. -/
theorem cast_choose_mul_mul (A B : ℕ) :
    (((p * A).choose (p * B) : ℕ) : k) = (A.choose B : k) := by
  apply CharP.natCast_eq_natCast' k p
  have hp0 : 0 < p := hp.out.pos
  have := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p * A) (k := p * B) (p := p)
  simpa [Nat.mul_mod_right, Nat.mul_div_cancel_left _ hp0] using this

include hp in
/-- Lucas' theorem: `C(p * A, j) ≡ 0` when `p ∤ j`. -/
theorem cast_choose_mul_of_not_dvd (A : ℕ) {j : ℕ} (hj : ¬ p ∣ j) :
    (((p * A).choose j : ℕ) : k) = 0 := by
  rw [CharP.cast_eq_zero_iff k p]
  apply (Nat.modEq_zero_iff_dvd).1
  have := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p * A) (k := j) (p := p)
  have hj0 : 0 < j % p := Nat.pos_of_ne_zero (fun h => hj (Nat.dvd_of_mod_eq_zero h))
  rw [Nat.mul_mod_right, Nat.choose_eq_zero_of_lt hj0, zero_mul] at this
  exact this

include hp in
/-- Lucas' theorem: `C(p * m - 1, p - 1) ≡ 1` for `m ≥ 1`. -/
theorem cast_choose_mul_sub_one (m : ℕ) (hm : 0 < m) :
    (((p * m - 1).choose (p - 1) : ℕ) : k) = 1 := by
  have hp0 : 0 < p := hp.out.pos
  have hmod : (p * m - 1) % p = p - 1 := by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [show p * (m + 1) - 1 = (p - 1) + p * m by rw [Nat.mul_succ]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p * m - 1) (k := p - 1) (p := p)
  rw [hmod, Nat.mod_eq_of_lt (by omega : p - 1 < p), Nat.div_eq_of_lt (by omega : p - 1 < p),
    Nat.choose_self, Nat.choose_zero_right, one_mul] at h
  have := CharP.natCast_eq_natCast' k p h
  rwa [Nat.cast_one] at this

include hp in
/-- Frobenius fixes the prime field: `powerSum (p * j) = powerSum j`. -/
theorem powerSum_mul (j : ℕ) : powerSum k p (p * j) = powerSum k p j := by
  unfold powerSum
  refine sum_congr rfl fun i _ => ?_
  have hi : (i : k) ^ p = i := by
    have := congrArg (ZMod.castHom (dvd_refl p) k) (ZMod.pow_card (i : ZMod p))
    rwa [map_pow, map_natCast] at this
  rw [pow_mul, hi]

omit [CharP k p] in
/-- Power sums over `ZMod p` agree with those over `range p`. -/
theorem sum_zmod_eq_sum_range (f : ZMod p → k) :
    ∑ x : ZMod p, f x = ∑ i ∈ range p, f i := by
  have hp0 : 0 < p := hp.out.pos
  symm
  refine sum_nbij (fun i => (i : ZMod p)) (by simp) ?_ ?_ (fun _ _ => rfl)
  · intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' a b p).1 hab
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro x _
    have : NeZero p := ⟨hp0.ne'⟩
    exact ⟨x.val, by simpa using ZMod.val_lt x, ZMod.natCast_zmod_val x⟩

include hp in
/-- Small power sums vanish. -/
theorem powerSum_eq_zero {j : ℕ} (hj : j < p - 1) : powerSum k p j = 0 := by
  have h := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) j (by simpa using hj)
  have := congrArg (ZMod.castHom (dvd_refl p) k) h
  rw [map_sum, map_zero, sum_zmod_eq_sum_range] at this
  simpa [powerSum] using this

include hp in
/-- The power sum of exponent `p - 1` is `-1`. -/
theorem powerSum_sub_one : powerSum k p (p - 1) = -1 := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have h := FiniteField.sum_pow_units (K := ZMod p) (p - 1)
  simp only [ZMod.card, dvd_refl, ↓reduceIte] at h
  have hs : ∑ x : ZMod p, x ^ (p - 1) = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ (p - 1)) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x : ZMod p => x ≠ 0)]
    have h0 : ∑ x : {x : ZMod p // ¬ x ≠ 0}, (x : ZMod p) ^ (p - 1) = 0 := by
      refine Fintype.sum_eq_zero _ fun x => ?_
      have := x.2; push Not at this
      rw [this, zero_pow (by have := hp.out.two_le; omega)]
    rw [h0, add_zero]
    exact (Fintype.sum_equiv (unitsEquivNeZero).symm _ _ (fun _ => rfl))
  have := congrArg (ZMod.castHom (dvd_refl p) k) (hs.trans h)
  rw [map_sum, map_neg, map_one, sum_zmod_eq_sum_range] at this
  simpa [powerSum] using this

include hp in
/-- In characteristic `p`, a homogeneous symmetric 2-cocycle satisfying the `p`-torsion
condition `∑_{i < p} c(i x, x) = 0` is a coboundary. -/
theorem IsHomCocycle.exists_eq_charP {n : ℕ} {d : ℕ → k} (h : IsHomCocycle n d)
    (ht : ∑ j ∈ range (n + 1), powerSum k p j * d j = 0) :
    ∃ g : k, ∀ i, 0 < i → i < n → d i = g * (n.choose i : k) := by
  have hp2 := hp.out.two_le
  induction n using Nat.strong_induction_on generalizing d with
  | _ n ih =>
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact ⟨0, fun i hi hin => by simp at hin⟩
      -- Step 1: the linear coefficient vanishes.
      have h1 : d 1 = 0 := by
        rcases Nat.lt_or_ge 1 m with hm2 | hm1
        · have hpm : p * 2 ≤ p * m := Nat.mul_le_mul_left p hm2
          have hc := h.coc 1 (p - 1) one_pos (by omega) (by omega)
          rw [show 1 + (p - 1) = p by omega, Nat.choose_one_right, CharP.cast_eq_zero, mul_zero,
            cast_choose_mul_sub_one p m hm, mul_one] at hc
          exact hc.symm
        · obtain rfl : m = 1 := by omega
          have hz : ∑ j ∈ range (p - 1), powerSum k p j * d j = 0 :=
            sum_eq_zero fun j hj => by rw [powerSum_eq_zero p (mem_range.1 hj), zero_mul]
          rw [show p * 1 + 1 = p - 1 + 1 + 1 by omega, sum_range_succ, sum_range_succ, hz,
            powerSum_sub_one p, show p - 1 + 1 = p * 1 by omega, h.top] at ht
          have hd : d (p - 1) = 0 := by simpa using ht
          rw [h.symm 1 (by omega), show p * 1 - 1 = p - 1 by omega]
          exact hd
      -- Step 2: coefficients of index prime to `p` vanish.
      have h2 : ∀ j, ¬ p ∣ j → j ≤ p * m → d j = 0 := by
        intro j hj hjn
        have hj0 : 0 < j := Nat.pos_of_ne_zero fun h0 => hj (h0 ▸ dvd_zero p)
        have hjn' : j < p * m := lt_of_le_of_ne hjn fun h0 => hj (h0 ▸ dvd_mul_right p m)
        have hjk : (j : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
        have := h.mul_eq hj0 hjn'
        rw [h1, zero_mul] at this
        exact (mul_eq_zero.1 this).resolve_left hjk
      -- Step 3: the coefficients of index divisible by `p` form a cocycle of degree `m`.
      have he : IsHomCocycle m (fun i => d (p * i)) := by
        refine ⟨by simpa using h.zero, h.top, fun i hi => ?_, fun a b ha hb hab => ?_⟩
        · show d (p * i) = d (p * (m - i))
          rw [h.symm (p * i) (Nat.mul_le_mul_left p hi), Nat.mul_sub]
        · show d (p * (a + b)) * _ = d (p * a) * _
          have hab' : p * (a + b) < p * m := Nat.mul_lt_mul_of_pos_left hab (by omega)
          have hc := h.coc (p * a) (p * b) (by positivity) (by positivity) (by rwa [← Nat.mul_add])
          rwa [← Nat.mul_add, ← Nat.mul_sub, cast_choose_mul_mul, cast_choose_mul_mul] at hc
      -- Step 4: the torsion condition descends.
      have hte : ∑ i ∈ range (m + 1), powerSum k p i * d (p * i) = 0 := by
        have hinj : Set.InjOn (fun i => p * i) (range (m + 1) : Set ℕ) :=
          fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (by omega) hab
        have hsub : (range (m + 1)).image (fun i => p * i) ⊆ range (p * m + 1) := by
          intro j hj
          simp only [mem_image, mem_range] at hj ⊢
          obtain ⟨i, hi, rfl⟩ := hj
          have : p * i ≤ p * m := Nat.mul_le_mul_left p (by omega)
          omega
        have hzero : ∀ j ∈ range (p * m + 1), j ∉ (range (m + 1)).image (fun i => p * i) →
            powerSum k p j * d j = 0 := by
          intro j hj hjn
          rw [mem_range] at hj
          have hpj : ¬ p ∣ j := by
            rintro ⟨i, rfl⟩
            refine hjn (mem_image.2 ⟨i, mem_range.2 ?_, rfl⟩)
            by_contra hi
            have : p * (m + 1) ≤ p * i := Nat.mul_le_mul_left p (by omega)
            rw [Nat.mul_succ] at this
            omega
          rw [h2 j hpj (by omega), mul_zero]
        rw [← ht, ← sum_subset hsub hzero, sum_image hinj]
        exact sum_congr rfl fun i _ => by rw [powerSum_mul]
      -- Step 5: induction.
      have hmn : m < p * m := by
        have : p * m ≥ 2 * m := Nat.mul_le_mul_right m hp2
        omega
      obtain ⟨g, hg⟩ := ih m hmn he hte
      refine ⟨g, fun j hj hjn => ?_⟩
      by_cases hpj : p ∣ j
      · obtain ⟨i, rfl⟩ := hpj
        have hi : 0 < i := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
        rw [hg i hi (Nat.lt_of_mul_lt_mul_left hjn), cast_choose_mul_mul]
      · rw [h2 j hpj hjn.le, cast_choose_mul_of_not_dvd p m hpj, mul_zero]
    · have hn : (n : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
      have key : ∀ i, 0 < i → i < n →
          (i : k) * d i = (i : k) * (d 1 / n * (n.choose i : k)) := by
        intro i hi hin
        rw [h.mul_eq hi hin, mul_left_comm, IsHomCocycle.cast_mul_choose hi (by omega)]
        field_simp
      refine ⟨d 1 / n, fun i hi hin => ?_⟩
      by_cases hpi : p ∣ i
      · have hni : ¬ p ∣ (n - i) := fun hd => hpn (by
          have := Nat.dvd_add hd hpi; rwa [Nat.sub_add_cancel hin.le] at this)
        have hi' : ((n - i : ℕ) : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
        rw [h.symm i hin.le, ← Nat.choose_symm hin.le]
        exact mul_left_cancel₀ hi' (key (n - i) (by omega) (by omega))
      · have hi' : (i : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
        exact mul_left_cancel₀ hi' (key i hi hin)

end CharP

end Langlands.Algebra.PolynomialCocycle
