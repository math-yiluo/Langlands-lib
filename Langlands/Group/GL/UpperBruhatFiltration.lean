import Mathlib.Algebra.BigOperators.Fin
import Langlands.Combinatorics.RelationInversions
import Langlands.Group.GL.UpperBruhatCells

/-!
# Inversion layers of actual upper Bruhat cells and the transpose index
-/

namespace Langlands.GeneralLinear

open Langlands.Combinatorics

universe u v

section Adapter

variable {α : Type v} (R : α → α → Prop) [DecidableRel R]

/-- Against the list of values of `f`, the related-pair count of one entry `a`
counts the positions `j` with `R a (f j)`. -/
theorem relationPairCount_singleton_ofFn (a : α) {m : ℕ} (f : Fin m → α) :
    relationPairCount R [a] (List.ofFn f) = ∑ j : Fin m, if R a (f j) then 1 else 0 := by
  simp [relationPairCount, Fin.sum_ofFn]

/-- The positional count `relationInversions` of the list of values of `f` is the
number of ordered index pairs `(i, j)` with `i < j` and `R (f i) (f j)`. -/
theorem relationInversions_ofFn_eq_card :
    ∀ {m : ℕ} (f : Fin m → α),
      relationInversions R (List.ofFn f) =
        (Finset.univ.filter fun p : Fin m × Fin m => p.1 < p.2 ∧ R (f p.1) (f p.2)).card
  | 0, f => by simp
  | m + 1, f => by
    rw [List.ofFn_succ, relationInversions_cons, relationPairCount_singleton_ofFn,
      relationInversions_ofFn_eq_card fun i => f i.succ, Finset.card_filter,
      Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_succ, Fin.succ_pos, Fin.not_lt_zero, Fin.succ_lt_succ_iff,
      false_and, true_and, ite_false, zero_add]

end Adapter

section Permutations

variable (n : ℕ)

/-- The ordered pairs `(i, j)` with `i < j` whose order is reversed by `w`. -/
def permutationInversions (w : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ w p.2 < w p.1

/-- The number of ordered pairs `(i, j)` with `i < j` and `w j < w i`: the
Library's positional count `relationInversions` for the relation `b < a`, applied
to the list `[w 0, ..., w (n - 1)]`. -/
def permutationInversionCount (w : Equiv.Perm (Fin n)) : ℕ :=
  relationInversions (fun a b : Fin n => b < a) (List.ofFn ⇑w)

/-- The adapter: the count is the specialization of `relationInversions`. -/
theorem permutationInversionCount_eq_relationInversions (w : Equiv.Perm (Fin n)) :
    permutationInversionCount n w =
      relationInversions (fun a b : Fin n => b < a) (List.ofFn ⇑w) :=
  rfl

theorem mem_permutationInversions_iff (w : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ permutationInversions n w ↔ p.1 < p.2 ∧ w p.2 < w p.1 := by
  simp only [permutationInversions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Agreement of the adapted count with the `Finset` of inverted ordered pairs. -/
theorem permutationInversionCount_eq_card_permutationInversions (w : Equiv.Perm (Fin n)) :
    permutationInversionCount n w = (permutationInversions n w).card :=
  relationInversions_ofFn_eq_card (fun a b : Fin n => b < a) ⇑w

theorem permutationInversionCount_eq_card (w : Equiv.Perm (Fin n)) :
    permutationInversionCount n w =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1).card :=
  permutationInversionCount_eq_card_permutationInversions n w

/-- The same count, as the cardinality of the subtype of inverted ordered pairs. -/
theorem permutationInversionCount_eq_fintypeCard (w : Equiv.Perm (Fin n)) :
    permutationInversionCount n w =
      Fintype.card {p : Fin n × Fin n // p.1 < p.2 ∧ w p.2 < w p.1} :=
  (permutationInversionCount_eq_card n w).trans (Fintype.card_subtype _).symm

theorem permutationInversionCount_one : permutationInversionCount n 1 = 0 := by
  rw [permutationInversionCount_eq_card_permutationInversions, Finset.card_eq_zero,
    Finset.eq_empty_iff_forall_notMem]
  rintro p hp
  rw [mem_permutationInversions_iff] at hp
  exact lt_asymm hp.1 hp.2

/-- The conjugate of `w⁻¹` by the order reversal: `Fin.revPerm * w⁻¹ * Fin.revPerm`. -/
def upperBruhatTransposeIndex (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm * w⁻¹ * Fin.revPerm

theorem upperBruhatTransposeIndex_apply (w : Equiv.Perm (Fin n)) (i : Fin n) :
    upperBruhatTransposeIndex n w i = (w⁻¹ i.rev).rev := by
  rw [upperBruhatTransposeIndex, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Fin.revPerm_apply, Fin.revPerm_apply]

theorem upperBruhatTransposeIndex_inv_apply (w : Equiv.Perm (Fin n)) (i : Fin n) :
    (upperBruhatTransposeIndex n w)⁻¹ i = (w i.rev).rev := by
  rw [Equiv.Perm.inv_eq_iff_eq, upperBruhatTransposeIndex_apply, Fin.rev_rev,
    Equiv.Perm.coe_inv, Equiv.symm_apply_apply, Fin.rev_rev]

/-- The transpose index is an involution on permutations. -/
theorem upperBruhatTransposeIndex_upperBruhatTransposeIndex (w : Equiv.Perm (Fin n)) :
    upperBruhatTransposeIndex n (upperBruhatTransposeIndex n w) = w := by
  ext i
  rw [upperBruhatTransposeIndex_apply, upperBruhatTransposeIndex_inv_apply,
    Fin.rev_rev, Fin.rev_rev]

theorem upperBruhatTransposeIndex_involutive :
    Function.Involutive (upperBruhatTransposeIndex n) :=
  upperBruhatTransposeIndex_upperBruhatTransposeIndex n

theorem upperBruhatTransposeIndex_one : upperBruhatTransposeIndex n 1 = 1 := by
  ext i
  rw [upperBruhatTransposeIndex_apply, inv_one, Equiv.Perm.one_apply, Fin.rev_rev,
    Equiv.Perm.one_apply]

end Permutations

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The matrix of the transpose index is `weylLong * p⁻¹ * weylLong`, with `p` the
matrix of `w`; this is only the homomorphism law, not a statement about cells. -/
theorem permutation_upperBruhatTransposeIndex (w : Equiv.Perm (Fin n)) :
    permutation n R (upperBruhatTransposeIndex n w) =
      weylLong n R * (permutation n R w)⁻¹ * weylLong n R := by
  rw [upperBruhatTransposeIndex, map_mul, map_mul, map_inv, weylLong]

/-- The union of the actual cells `C_w` with at most `k` inversions. -/
def upperBruhatLayerLE (k : ℕ) : Set (Langlands.GeneralLinear n R) :=
  {g | ∃ w : Equiv.Perm (Fin n),
    permutationInversionCount n w ≤ k ∧ g ∈ upperBruhatCell n R w}

theorem mem_upperBruhatLayerLE_iff (k : ℕ) (g : Langlands.GeneralLinear n R) :
    g ∈ upperBruhatLayerLE n R k ↔
      ∃ w : Equiv.Perm (Fin n),
        permutationInversionCount n w ≤ k ∧ g ∈ upperBruhatCell n R w :=
  Iff.rfl

theorem upperBruhatLayerLE_eq_iUnion (k : ℕ) :
    upperBruhatLayerLE n R k =
      ⋃ (w : Equiv.Perm (Fin n)) (_ : permutationInversionCount n w ≤ k),
        upperBruhatCell n R w := by
  ext g
  simp only [mem_upperBruhatLayerLE_iff, Set.mem_iUnion, exists_prop]

theorem upperBruhatCell_subset_upperBruhatLayerLE (w : Equiv.Perm (Fin n)) {k : ℕ}
    (hw : permutationInversionCount n w ≤ k) :
    upperBruhatCell n R w ⊆ upperBruhatLayerLE n R k :=
  fun _ hg => ⟨w, hw, hg⟩

/-- The layers increase with the inversion bound. -/
theorem upperBruhatLayerLE_mono : Monotone (upperBruhatLayerLE n R) :=
  fun _ _ hkl _ ⟨w, hw, hg⟩ => ⟨w, hw.trans hkl, hg⟩

theorem upperBruhatLayerLE_subset {k l : ℕ} (hkl : k ≤ l) :
    upperBruhatLayerLE n R k ⊆ upperBruhatLayerLE n R l :=
  upperBruhatLayerLE_mono n R hkl

/-- The union of the actual cells `C_v` with strictly more inversions than `w`. -/
def upperBruhatHigherCells (w : Equiv.Perm (Fin n)) : Set (Langlands.GeneralLinear n R) :=
  {g | ∃ v : Equiv.Perm (Fin n),
    permutationInversionCount n w < permutationInversionCount n v ∧
      g ∈ upperBruhatCell n R v}

theorem mem_upperBruhatHigherCells_iff (w : Equiv.Perm (Fin n))
    (g : Langlands.GeneralLinear n R) :
    g ∈ upperBruhatHigherCells n R w ↔
      ∃ v : Equiv.Perm (Fin n),
        permutationInversionCount n w < permutationInversionCount n v ∧
          g ∈ upperBruhatCell n R v :=
  Iff.rfl

theorem upperBruhatCell_subset_upperBruhatHigherCells {w v : Equiv.Perm (Fin n)}
    (hwv : permutationInversionCount n w < permutationInversionCount n v) :
    upperBruhatCell n R v ⊆ upperBruhatHigherCells n R w :=
  fun _ hg => ⟨v, hwv, hg⟩

/-- The actual cell `C_w` together with all cells having more inversions. -/
def upperBruhatCellNeighborhood (w : Equiv.Perm (Fin n)) :
    Set (Langlands.GeneralLinear n R) :=
  upperBruhatCell n R w ∪ upperBruhatHigherCells n R w

theorem mem_upperBruhatCellNeighborhood_iff (w : Equiv.Perm (Fin n))
    (g : Langlands.GeneralLinear n R) :
    g ∈ upperBruhatCellNeighborhood n R w ↔
      g ∈ upperBruhatCell n R w ∨ g ∈ upperBruhatHigherCells n R w :=
  Iff.rfl

theorem upperBruhatCell_subset_upperBruhatCellNeighborhood (w : Equiv.Perm (Fin n)) :
    upperBruhatCell n R w ⊆ upperBruhatCellNeighborhood n R w :=
  Set.subset_union_left

theorem upperBruhatHigherCells_subset_upperBruhatCellNeighborhood
    (w : Equiv.Perm (Fin n)) :
    upperBruhatHigherCells n R w ⊆ upperBruhatCellNeighborhood n R w :=
  Set.subset_union_right

end Langlands.GeneralLinear
