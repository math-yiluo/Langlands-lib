import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort

/-!
# A tightness criterion for families of column sets

Let `D j` (`j < N`) be sets of columns of `Fin n`. For a column `x`, `colSet D x` is the set of
rows `j` with `x ∈ D j`. This module proves a rigidity statement used in the scalar step for
discrete-series blocks: if a family `D` has the same row cardinalities as a family `D'` whose
column sets are initial segments `{0, …, c_x - 1}`, and every column set of `D` has at least
`c_x` elements, then `D = D'`.

The proof counts the incidences `x ∈ D j` twice, once with weight `1` and once with weight `j`.
A set of `c` rows has weight sum at least `0 + 1 + … + (c - 1)`, with equality only for the
initial segment.
-/

namespace Langlands.Archimedean

namespace RealDiscreteTightness

open Finset

variable {n N : ℕ}

/-- The rows `j` whose column set contains the column `x`. -/
def colSet (D : Fin N → Finset (Fin n)) (x : Fin n) : Finset (Fin N) :=
  univ.filter fun j => x ∈ D j

/-- The initial segment `{0, …, c - 1}` of `Fin N`. -/
def seg (N c : ℕ) : Finset (Fin N) :=
  univ.filter fun j => (j : ℕ) < c

theorem mem_colSet {D : Fin N → Finset (Fin n)} {x : Fin n} {j : Fin N} :
    j ∈ colSet D x ↔ x ∈ D j := by
  simp [colSet]

theorem mem_seg {c : ℕ} {j : Fin N} : j ∈ seg N c ↔ (j : ℕ) < c := by
  simp [seg]

/-! ## Double counting -/

theorem sum_card_eq (D : Fin N → Finset (Fin n)) :
    ∑ j, (D j).card = ∑ x, (colSet D x).card := by
  have h1 : ∀ j, (D j).card = ∑ x : Fin n, if x ∈ D j then 1 else 0 := by
    intro j
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp
  have h2 : ∀ x, (colSet D x).card = ∑ j : Fin N, if x ∈ D j then 1 else 0 := by
    intro x
    rw [colSet, Finset.card_filter]
  simp only [h1, h2]
  exact Finset.sum_comm

theorem sum_weight_eq (D : Fin N → Finset (Fin n)) :
    ∑ j : Fin N, (j : ℕ) * (D j).card = ∑ x, ∑ j ∈ colSet D x, (j : ℕ) := by
  have h1 : ∀ j : Fin N, (j : ℕ) * (D j).card = ∑ x : Fin n, if x ∈ D j then (j : ℕ) else 0 := by
    intro j
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    congr 2
    ext x
    simp
  have h2 : ∀ x, ∑ j ∈ colSet D x, (j : ℕ) = ∑ j : Fin N, if x ∈ D j then (j : ℕ) else 0 := by
    intro x
    rw [colSet, Finset.sum_filter]
  simp only [h1, h2]
  exact Finset.sum_comm

/-! ## Initial segments -/

theorem map_seg {c : ℕ} (hc : c ≤ N) : (seg N c).map Fin.valEmbedding = range c := by
  ext i
  simp only [mem_map, mem_seg, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hi
    exact ⟨⟨i, by omega⟩, hi, rfl⟩

theorem card_seg {c : ℕ} (hc : c ≤ N) : (seg N c).card = c := by
  rw [← card_map Fin.valEmbedding, map_seg hc, card_range]

theorem sum_seg {c : ℕ} (hc : c ≤ N) : ∑ j ∈ seg N c, (j : ℕ) = ∑ i ∈ range c, i := by
  rw [← map_seg hc, sum_map]
  rfl

theorem val_le_of_strictMono {m : ℕ} {f : Fin m → Fin N} (hf : StrictMono f) :
    ∀ i : Fin m, (i : ℕ) ≤ f i := by
  rintro ⟨i, hi⟩
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have h1 := ih (by omega)
    have h2 : f ⟨i, by omega⟩ < f ⟨i + 1, hi⟩ := hf (by rw [Fin.lt_def]; simp)
    rw [Fin.lt_def] at h2
    simp only at h1 ⊢
    omega

theorem sum_orderEmbOfFin (E : Finset (Fin N)) :
    ∑ j ∈ E, (j : ℕ) = ∑ i : Fin E.card, (E.orderEmbOfFin rfl i : ℕ) := by
  conv_lhs => rw [← map_orderEmbOfFin_univ E rfl, sum_map]
  rfl

/-- A set of `c` rows has weight sum at least `0 + 1 + … + (c - 1)`. -/
theorem sum_range_le_sum (E : Finset (Fin N)) :
    ∑ i ∈ range E.card, i ≤ ∑ j ∈ E, (j : ℕ) := by
  rw [sum_orderEmbOfFin, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => val_le_of_strictMono (E.orderEmbOfFin rfl).strictMono i

/-- Equality holds only for the initial segment. -/
theorem eq_seg_of_sum {E : Finset (Fin N)} {c : ℕ} (hc : E.card = c)
    (hs : ∑ j ∈ E, (j : ℕ) = ∑ i ∈ range c, i) : E = seg N c := by
  subst hc
  rw [sum_orderEmbOfFin, ← Fin.sum_univ_eq_sum_range] at hs
  have hle : ∀ i ∈ (univ : Finset (Fin E.card)),
      (i : ℕ) ≤ (E.orderEmbOfFin rfl i : ℕ) :=
    fun i _ => val_le_of_strictMono (E.orderEmbOfFin rfl).strictMono i
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hs.symm
  ext j
  rw [mem_seg]
  constructor
  · intro hj
    have hr : j ∈ Set.range (E.orderEmbOfFin rfl) := by
      rw [range_orderEmbOfFin]
      exact hj
    obtain ⟨i, rfl⟩ := hr
    rw [← heq i (mem_univ _)]
    exact i.2
  · intro hj
    have h := heq ⟨j, hj⟩ (mem_univ _)
    have hj' : E.orderEmbOfFin rfl ⟨j, hj⟩ = j := Fin.ext h.symm
    rw [← hj']
    exact orderEmbOfFin_mem _ _ _

/-! ## The tightness criterion -/

/-- **Tightness.** If `D` and `D'` have the same row cardinalities, every column set of `D'` is
an initial segment `{0, …, c_x - 1}`, and every column set of `D` has at least `c_x` elements,
then `D = D'`. -/
theorem eq_of_tight {D D' : Fin N → Finset (Fin n)} (h1 : ∀ j, (D j).card = (D' j).card)
    (h2 : ∀ x, ∃ c ≤ (colSet D x).card, c ≤ N ∧ colSet D' x = seg N c) : D = D' := by
  choose c hcle hcN hseg using h2
  have hc' : ∀ x, (colSet D' x).card = c x := fun x => by rw [hseg, card_seg (hcN x)]
  have hsum : ∑ x, c x = ∑ x, (colSet D x).card := by
    rw [← sum_card_eq, Finset.sum_congr rfl fun j _ => h1 j, sum_card_eq]
    exact Finset.sum_congr rfl fun x _ => (hc' x).symm
  have hcard : ∀ x, (colSet D x).card = c x := fun x =>
    ((Finset.sum_eq_sum_iff_of_le fun x _ => hcle x).mp hsum x (mem_univ x)).symm
  have hw : ∑ x, ∑ j ∈ colSet D' x, (j : ℕ) = ∑ x, ∑ j ∈ colSet D x, (j : ℕ) := by
    rw [← sum_weight_eq, ← sum_weight_eq]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]
  have hle : ∀ x ∈ (univ : Finset (Fin n)),
      ∑ j ∈ colSet D' x, (j : ℕ) ≤ ∑ j ∈ colSet D x, (j : ℕ) := by
    intro x _
    rw [hseg, sum_seg (hcN x), ← hcard x]
    exact sum_range_le_sum (colSet D x)
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hw
  have hE : ∀ x, colSet D x = colSet D' x := by
    intro x
    rw [hseg]
    refine eq_seg_of_sum (hcard x) ?_
    rw [← sum_seg (hcN x), ← hseg]
    exact (heq x (mem_univ _)).symm
  funext j
  ext x
  rw [← mem_colSet (D := D), hE x, mem_colSet]

end RealDiscreteTightness

end Langlands.Archimedean
