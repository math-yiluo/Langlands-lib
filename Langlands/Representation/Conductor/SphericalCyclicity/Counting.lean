import Langlands.Representation.Conductor.SphericalCyclicity.LinearAlgebra

/-!
# Counting tuples by the position of their last nonzero entry

For a tuple `c : Fin m → k` over a finite type with a zero, `top c` is one plus the
largest index of a nonzero entry (and `0` when `c = 0`).  We compute the sum of
`φ (max j (top c))` over all tuples and compare it with the rows of `cellMatrix`.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open scoped BigOperators
open Matrix

variable {k : Type*} [Zero k] [DecidableEq k]

/-- One plus the largest index of a nonzero entry of `c`, or `0` if `c = 0`. -/
def top : {m : ℕ} → (Fin m → k) → ℕ
  | 0, _ => 0
  | m + 1, c => if c (Fin.last m) = 0 then top (Fin.init c) else m + 1

theorem top_zero_length (c : Fin 0 → k) : top c = 0 := rfl

theorem top_succ {m : ℕ} (c : Fin (m + 1) → k) :
    top c = if c (Fin.last m) = 0 then top (Fin.init c) else m + 1 := rfl

theorem top_snoc {m : ℕ} (c : Fin m → k) (x : k) :
    top (Fin.snoc c x : Fin (m + 1) → k) = if x = 0 then top c else m + 1 := by
  rw [top_succ, Fin.snoc_last, Fin.init_snoc]

theorem top_le_iff {m : ℕ} (c : Fin m → k) (t : ℕ) :
    top c ≤ t ↔ ∀ i : Fin m, t ≤ (i : ℕ) → c i = 0 := by
  induction m with
  | zero =>
    rw [top_zero_length]
    exact ⟨fun _ i => i.elim0, fun _ => Nat.zero_le t⟩
  | succ m ih =>
    rw [top_succ]
    by_cases h : c (Fin.last m) = 0
    · rw [if_pos h, ih]
      constructor
      · intro H i
        refine Fin.lastCases (fun _ => h) (fun i hi => ?_) i
        exact H i (by simpa using hi)
      · intro H i hi
        exact H i.castSucc (by simpa using hi)
    · rw [if_neg h]
      constructor
      · intro H i hi
        exact absurd (lt_of_lt_of_le i.isLt (H.trans hi)) (lt_irrefl _)
      · intro H
        by_contra hlt
        exact h (H (Fin.last m) (by simp; omega))

theorem top_le {m : ℕ} (c : Fin m → k) : top c ≤ m :=
  (top_le_iff c m).2 fun i hi => absurd i.isLt (not_lt.2 hi)

theorem eq_zero_of_top_le {m : ℕ} (c : Fin m → k) (i : Fin m) (hi : top c ≤ (i : ℕ)) :
    c i = 0 :=
  (top_le_iff c (top c)).1 le_rfl i hi

theorem ne_zero_of_top_eq {m : ℕ} (c : Fin m → k) (i : Fin m) (h : top c = (i : ℕ) + 1) :
    c i ≠ 0 := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    rw [top_succ] at h
    by_cases hl : c (Fin.last m) = 0
    · rw [if_pos hl] at h
      have hle := top_le (Fin.init c)
      have hi : (i : ℕ) < m := by omega
      have := ih (Fin.init c) ⟨i, hi⟩ (by simpa using h)
      simpa [Fin.init] using this
    · rw [if_neg hl] at h
      have : i = Fin.last m := Fin.ext (by simp; omega)
      rw [this]
      exact hl

variable [Fintype k]

theorem sum_top_succ {R : Type*} [CommRing R] {m : ℕ} (φ : ℕ → R) :
    ∑ c : Fin (m + 1) → k, φ (top c) =
      ∑ c : Fin m → k, φ (top c) +
        ((Fintype.card k : R) - 1) * (Fintype.card k : R) ^ m * φ (m + 1) := by
  rw [← (Fin.snocEquiv (fun _ => k)).sum_comp, Fintype.sum_prod_type]
  change ∑ x : k, ∑ c : Fin m → k, φ (top (Fin.snoc c x : Fin (m + 1) → k)) = _
  have h : ∀ x : k, ∑ c : Fin m → k, φ (top (Fin.snoc c x : Fin (m + 1) → k)) =
      (Fintype.card k : R) ^ m * φ (m + 1) +
        if x = 0 then ∑ c : Fin m → k, φ (top c) - (Fintype.card k : R) ^ m * φ (m + 1)
        else 0 := by
    intro x
    simp only [top_snoc]
    by_cases hx : x = 0
    · simp only [hx, ↓reduceIte]
      ring
    · simp only [hx, if_false, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, add_zero]
      push_cast
      ring
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The sum of `φ (max J (top c))`, multiplied by the cardinality `q` of `k`. -/
theorem sum_max_top {R : Type*} [CommRing R] (φ : ℕ → R) (J : ℕ) :
    ∀ m, J ≤ m →
      (Fintype.card k : R) * ∑ c : Fin m → k, φ (max J (top c)) =
        (Fintype.card k : R) ^ (J + 1) * φ J +
          ∑ i ∈ Finset.range (m + 1),
            if J < i then ((Fintype.card k : R) - 1) * (Fintype.card k : R) ^ i * φ i
            else 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have hmax : ∀ c : Fin J → k, max J (top c) = J := fun c => max_eq_left (top_le c)
    simp only [hmax, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul]
    rw [Finset.sum_eq_zero (fun i hi => if_neg (by simp at hi; omega))]
    push_cast
    ring
  | succ m hJm ih =>
    have hs := sum_top_succ (k := k) (m := m) (fun t => φ (max J t))
    rw [hs, mul_add, ih, Finset.sum_range_succ _ (m + 1), if_pos (by omega),
      max_eq_right (by omega : J ≤ m + 1)]
    ring

/-- The rows of `cellMatrix`, cleared of their leading factor. -/
theorem cellMatrix_mulVec_row {r q : ℕ} (z : Fin r → ℂ) (a : Fin r → ℂ) (j : Fin r)
    (hz : z j ≠ 0) (hq : (q : ℂ) ≠ 0) :
    z j * (q : ℂ) ^ ((j : ℕ) + 1) * (cellMatrix r q z *ᵥ a) j =
      (q : ℂ) ^ ((j : ℕ) + 1) * a j +
        ∑ i : Fin r, if j < i then ((q : ℂ) - 1) * (q : ℂ) ^ (i : ℕ) * a i else 0 := by
  have hne : z j * (q : ℂ) ^ ((j : ℕ) + 1) ≠ 0 := mul_ne_zero hz (pow_ne_zero _ hq)
  simp only [Matrix.mulVec, dotProduct, cellMatrix]
  rw [Finset.mul_sum]
  have hpt : ∀ i : Fin r, z j * (q : ℂ) ^ ((j : ℕ) + 1) *
      ((z j * (q : ℂ) ^ ((j : ℕ) + 1))⁻¹ *
        (if j = i then (q : ℂ) ^ ((j : ℕ) + 1)
          else if j < i then ((q : ℂ) - 1) * (q : ℂ) ^ (i : ℕ) else 0) * a i) =
      (if j = i then (q : ℂ) ^ ((j : ℕ) + 1) * a j else 0) +
        (if j < i then ((q : ℂ) - 1) * (q : ℂ) ^ (i : ℕ) * a i else 0) := by
    intro i
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    by_cases hji : j = i
    · subst hji
      simp
    · simp only [hji, if_false, zero_add]
      split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

/-- The index `max j (top c)`, as an element of `Fin (n + 2)`. -/
def cellIndex {n : ℕ} (j : Fin (n + 2)) (c : Fin (n + 1) → k) : Fin (n + 2) :=
  ⟨max (j : ℕ) (top c), by have := top_le c; have := j.isLt; omega⟩

omit [Fintype k] in
theorem cellIndex_val {n : ℕ} (j : Fin (n + 2)) (c : Fin (n + 1) → k) :
    (cellIndex j c : ℕ) = max (j : ℕ) (top c) := rfl

/-- Summing the values at `cellIndex j c` over all tuples gives `z j q^j` times the
`j`-th row of `cellMatrix`. -/
theorem sum_cellIndex {n q : ℕ} (hk : Fintype.card k = q) (z : Fin (n + 2) → ℂ)
    (hz : ∀ i, z i ≠ 0) (a : Fin (n + 2) → ℂ) (j : Fin (n + 2)) :
    ∑ c : Fin (n + 1) → k, a (cellIndex j c) =
      z j * (q : ℂ) ^ (j : ℕ) * (cellMatrix (n + 2) q z *ᵥ a) j := by
  have hq0 : (q : ℂ) ≠ 0 := by
    rw [← hk]
    exact_mod_cast Fintype.card_ne_zero (α := k)
  set a' : ℕ → ℂ := fun t => if h : t < n + 2 then a ⟨t, h⟩ else 0 with ha'
  have hcell : ∀ c : Fin (n + 1) → k, a (cellIndex j c) = a' (max (j : ℕ) (top c)) := by
    intro c
    rw [ha']
    simp only
    rw [dif_pos (show max (j : ℕ) (top c) < n + 2 from (cellIndex j c).isLt)]
    rfl
  have hfin : ∀ i : Fin (n + 2), a i = a' i := by
    intro i
    rw [ha']
    simp only
    rw [dif_pos i.isLt]
  have hsum := sum_max_top (k := k) a' (j : ℕ) (n + 1) (by omega)
  rw [hk] at hsum
  have hrow := cellMatrix_mulVec_row z a j (hz j) hq0
  apply mul_left_cancel₀ hq0
  rw [Finset.sum_congr rfl (fun c _ => hcell c), hsum]
  have e1 : (q : ℂ) * (z j * (q : ℂ) ^ (j : ℕ) * (cellMatrix (n + 2) q z *ᵥ a) j) =
      z j * (q : ℂ) ^ ((j : ℕ) + 1) * (cellMatrix (n + 2) q z *ᵥ a) j := by ring
  rw [e1, hrow, ← hfin j]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if (j : ℕ) < i then ((q : ℂ) - 1) * (q : ℂ) ^ i * a' i else 0) (n + 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← hfin i]
  exact if_congr Fin.lt_def.symm rfl rfl

end Langlands.Conductor.SphericalCyclicity
