import Langlands.Group.GL.AdjacentMergeShape

/-! Consecutive triple merges and their exact ordered refinements. -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GeneralLinear.BlockShape

open Geometric

variable {n : ℕ}

private theorem sum_fin_eq_one (L : ℕ) (hL : L = 1) (f : Fin L → ℕ) :
    ∑ k, f k = f ⟨0, by omega⟩ := by
  subst hL
  exact Fin.sum_univ_one f

private theorem sum_fin_eq_three (L : ℕ) (hL : L = 3) (f : Fin L → ℕ) :
    ∑ k, f k = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ := by
  subst hL
  simp [Fin.sum_univ_succ, Nat.add_assoc]


section Triple

variable (B : BlockShape n) (j : ℕ) (h : j + 2 < B.length)

/-- Three original blocks at slot `j`, and one at every other coarse slot. -/
def tripleInnerLength (m : Fin (B.length - 2)) : ℕ := if m.val = j then 3 else 1

private theorem sum_range_triple (m : ℕ) :
    ∑ i ∈ Finset.range m, (if i = j then 3 else 1) = m + if j < m then 2 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

private theorem sum_tripleInnerLength_castLE (m : ℕ) (hm : m ≤ B.length - 2) :
    ∑ i : Fin m, B.tripleInnerLength j (Fin.castLE hm i) =
      m + if j < m then 2 else 0 :=
  (Fin.sum_univ_eq_sum_range (fun i => if i = j then 3 else 1) m).trans
    (sum_range_triple j m)

include h in
/-- The original triple and all singleton blocks exhaust the original labels. -/
theorem sum_tripleInnerLength : ∑ m, B.tripleInnerLength j m = B.length := by
  calc
    ∑ m, B.tripleInnerLength j m =
        ∑ i ∈ Finset.range (B.length - 2), (if i = j then 3 else 1) :=
      Fin.sum_univ_eq_sum_range (fun i => if i = j then 3 else 1) _
    _ = B.length := by
      rw [sum_range_triple, ite_eq_left (by omega)]
      omega

/-- Original block numbering of the triple refinement, in consecutive order. -/
def tripleLabelEquiv :
    ((m : Fin (B.length - 2)) × Fin (B.tripleInnerLength j m)) ≃ Fin B.length :=
  finSigmaFinEquiv.trans (finCongr (B.sum_tripleInnerLength j h))

theorem tripleLabelEquiv_val
    (q : (m : Fin (B.length - 2)) × Fin (B.tripleInnerLength j m)) :
    (B.tripleLabelEquiv j h q).val =
      q.1.val + q.2.val + if j < q.1.val then 2 else 0 := by
  rw [tripleLabelEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply, B.sum_tripleInnerLength_castLE j]
  omega

/-- The rank of each coarse block is the sum of precisely its original ranks. -/
def tripleMergeSize (m : Fin (B.length - 2)) : ℕ :=
  ∑ k : Fin (B.tripleInnerLength j m), B.size (B.tripleLabelEquiv j h ⟨m, k⟩)

theorem tripleMergeSize_pos (m : Fin (B.length - 2)) :
    0 < B.tripleMergeSize j h m := by
  have hlen : 0 < B.tripleInnerLength j m := by
    unfold tripleInnerLength
    split_ifs <;> omega
  exact Finset.sum_pos (fun k _ => B.positive _)
    ⟨⟨0, hlen⟩, Finset.mem_univ _⟩

/-- Merge the three consecutive slots, retaining all other blocks in order. -/
def tripleMerge : BlockShape n where
  length := B.length - 2
  size := B.tripleMergeSize j h
  positive := B.tripleMergeSize_pos j h
  sum_eq := by
    calc
      ∑ m, B.tripleMergeSize j h m =
          ∑ q, B.size (B.tripleLabelEquiv j h q) :=
        (Fintype.sum_sigma fun q => B.size (B.tripleLabelEquiv j h q)).symm
      _ = ∑ b, B.size b := Equiv.sum_comp _ _
      _ = n := B.sum_eq

/-- The original blocks inside each triple-merged block. -/
def tripleRefinement : BlockRefinement (B.tripleMerge j h) := fun m =>
  { length := B.tripleInnerLength j m
    size := fun k => B.size (B.tripleLabelEquiv j h ⟨m, k⟩)
    positive := fun _ => B.positive _
    sum_eq := rfl }

/-- The consecutive nested labels of the actual triple refinement. -/
def tripleBlockEquiv :
    ((i : Fin (B.tripleMerge j h).length) × Fin (B.tripleRefinement j h i).length) ≃
      Fin B.length :=
  B.tripleLabelEquiv j h

theorem tripleBlock_size
    (a : (i : Fin (B.tripleMerge j h).length) × Fin (B.tripleRefinement j h i).length) :
    (B.tripleRefinement j h a.1).size a.2 =
      B.size (B.tripleBlockEquiv j h a) := rfl

theorem tripleBlockEquiv_val
    (a : (i : Fin (B.tripleMerge j h).length) × Fin (B.tripleRefinement j h i).length) :
    (B.tripleBlockEquiv j h a).val =
      a.1.val + a.2.val + if j < a.1.val then 2 else 0 :=
  B.tripleLabelEquiv_val j h a

/-- The original labels have exactly the lexicographic nested order. -/
theorem tripleBlockEquiv_lt_iff
    (a b : (i : Fin (B.tripleMerge j h).length) × Fin (B.tripleRefinement j h i).length) :
    B.tripleBlockEquiv j h a < B.tripleBlockEquiv j h b ↔
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val) := by
  rcases a with ⟨⟨m, hm⟩, k⟩
  rcases b with ⟨⟨m', hm'⟩, k'⟩
  have hk : k.val < if m = j then 3 else 1 := k.isLt
  have hk' : k'.val < if m' = j then 3 else 1 := k'.isLt
  rw [Fin.lt_def, tripleBlockEquiv_val, tripleBlockEquiv_val, Fin.lt_def, Fin.ext_iff]
  dsimp only
  split_ifs at hk hk' ⊢ <;> omega

/-- The exact standard-coordinate identity of the triple refinement. -/
theorem triple_index (i : Fin (B.tripleMerge j h).length)
    (k : Fin (B.tripleRefinement j h i).length)
    (x : Fin ((B.tripleRefinement j h i).size k)) :
    (B.tripleMerge j h).index i ((B.tripleRefinement j h i).index k x) =
      B.index (B.tripleBlockEquiv j h ⟨i, k⟩)
        (Fin.cast (B.tripleBlock_size j h ⟨i, k⟩) x) :=
  index_index_eq_of_lex B (B.tripleMerge j h) (B.tripleRefinement j h)
    (B.tripleBlockEquiv j h) (B.tripleBlock_size j h)
    (fun a b hab => (B.tripleBlockEquiv_lt_iff j h a b).mpr hab) i k x

@[simp] theorem tripleMerge_length : (B.tripleMerge j h).length = B.length - 2 := rfl

/-- The coarse slot containing the three selected blocks. -/
def tripleMergeIndex : Fin (B.tripleMerge j h).length :=
  ⟨j, by change j < B.length - 2; omega⟩

@[simp] theorem tripleMergeIndex_val : (B.tripleMergeIndex j h).val = j := rfl

theorem tripleRefinement_length (m : Fin (B.tripleMerge j h).length) :
    (B.tripleRefinement j h m).length = if m.val = j then 3 else 1 := rfl

theorem tripleRefinement_length_merged :
    (B.tripleRefinement j h (B.tripleMergeIndex j h)).length = 3 := ite_eq_left rfl

theorem tripleRefinement_length_of_ne (m : Fin (B.tripleMerge j h).length)
    (hm : m.val ≠ j) : (B.tripleRefinement j h m).length = 1 := ite_eq_right hm

theorem tripleRefinement_size_merged
    (k : Fin (B.tripleRefinement j h (B.tripleMergeIndex j h)).length) :
    (B.tripleRefinement j h (B.tripleMergeIndex j h)).size k =
      B.size ⟨j + k.val, by
        have := k.isLt
        have := B.tripleRefinement_length_merged j h
        omega⟩ := by
  change B.size (B.tripleBlockEquiv j h ⟨B.tripleMergeIndex j h, k⟩) = _
  congr 1
  apply Fin.ext
  rw [tripleBlockEquiv_val]
  simp

/-- The selected coarse block has the sum of the three selected ranks. -/
theorem tripleMerge_size_merged :
    (B.tripleMerge j h).size (B.tripleMergeIndex j h) =
      B.size ⟨j, by omega⟩ + B.size ⟨j + 1, by omega⟩ + B.size ⟨j + 2, h⟩ := by
  rw [← (B.tripleRefinement j h (B.tripleMergeIndex j h)).sum_eq,
    sum_fin_eq_three _ (B.tripleRefinement_length_merged j h)]
  simp only [tripleRefinement_size_merged, Nat.add_zero]

/-- An outside coarse block retains its unique original block rank. -/
theorem tripleMerge_size_of_ne (m : Fin (B.tripleMerge j h).length)
    (hm : m.val ≠ j) :
    (B.tripleMerge j h).size m =
      B.size ⟨m.val + if j < m.val then 2 else 0, by
        have hlen : m.val < B.length - 2 := m.isLt
        split_ifs <;> omega⟩ := by
  rw [← (B.tripleRefinement j h m).sum_eq,
    sum_fin_eq_one _ (B.tripleRefinement_length_of_ne j h m hm)]
  change B.size (B.tripleBlockEquiv j h ⟨m, ⟨0, _⟩⟩) = _
  congr 1
  apply Fin.ext
  rw [tripleBlockEquiv_val]
  simp

/-- An outside refined block has the rank of the entire outside coarse block. -/
theorem tripleRefinement_size_of_ne (m : Fin (B.tripleMerge j h).length)
    (hm : m.val ≠ j) (k : Fin (B.tripleRefinement j h m).length) :
    (B.tripleRefinement j h m).size k = (B.tripleMerge j h).size m := by
  have hsum := (B.tripleRefinement j h m).sum_eq
  rw [Finset.sum_eq_single k] at hsum
  · exact hsum
  · intro k' _ hk'
    have h₁ := k.isLt
    have h₂ := k'.isLt
    have hl := B.tripleRefinement_length_of_ne j h m hm
    exact absurd (Fin.ext (by omega)) hk'
  · simp

section Swap

variable (δ : ℕ) (hδ : δ ≤ 1)

private theorem triple_swap_fixes_outside
    (m : Fin (B.tripleMerge j h).length) (hm : m.val ≠ j)
    (k : Fin (B.tripleRefinement j h m).length) :
    B.adjacentSwap (j + δ) (by omega) (B.tripleBlockEquiv j h ⟨m, k⟩) =
      B.tripleBlockEquiv j h ⟨m, k⟩ := by
  have hk : k.val < 1 := (B.tripleRefinement_length_of_ne j h m hm) ▸ k.isLt
  have hv := B.tripleBlockEquiv_val j h ⟨m, k⟩
  dsimp only at hv
  apply Equiv.swap_apply_of_ne_of_ne <;>
    simp only [ne_eq, Fin.ext_iff] <;> split_ifs at hv <;> omega

/-- Swapping either adjacent pair within the selected triple preserves
every coarse rank. -/
theorem tripleMergeSize_permute_adjacentSwap (m : Fin (B.length - 2)) :
    (B.permute (B.adjacentSwap (j + δ) (by omega))).tripleMergeSize j h m =
      B.tripleMergeSize j h m := by
  by_cases hm : m.val = j
  · have hm' : m = B.tripleMergeIndex j h := Fin.ext hm
    subst m
    change
      ((B.permute (B.adjacentSwap (j + δ) (by omega))).tripleMerge j h).size
          ((B.permute (B.adjacentSwap (j + δ) (by omega))).tripleMergeIndex j h) =
        (B.tripleMerge j h).size (B.tripleMergeIndex j h)
    rw [(B.permute (B.adjacentSwap (j + δ) (by omega))).tripleMerge_size_merged j h,
      B.tripleMerge_size_merged j h]
    by_cases hd : δ = 0
    · subst δ
      simp only [Nat.add_zero]
      change
        B.size (B.adjacentSwap j _ ⟨j, _⟩) +
            B.size (B.adjacentSwap j _ ⟨j + 1, _⟩) +
            B.size (B.adjacentSwap j _ ⟨j + 2, _⟩) = _
      have hc : B.adjacentSwap j (by omega) ⟨j + 2, h⟩ = ⟨j + 2, h⟩ := by
        apply Equiv.swap_apply_of_ne_of_ne <;>
          simp only [ne_eq, Fin.ext_iff] <;> omega
      rw [hc, adjacentSwap, Equiv.swap_apply_left, Equiv.swap_apply_right]
      omega
    · have hd : δ = 1 := by omega
      subst δ
      change
        B.size (B.adjacentSwap (j + 1) _ ⟨j, _⟩) +
            B.size (B.adjacentSwap (j + 1) _ ⟨j + 1, _⟩) +
            B.size (B.adjacentSwap (j + 1) _ ⟨j + 2, _⟩) = _
      have ha : B.adjacentSwap (j + 1) (by omega) ⟨j, by omega⟩ = ⟨j, by omega⟩ := by
        apply Equiv.swap_apply_of_ne_of_ne <;>
          simp only [ne_eq, Fin.ext_iff] <;> omega
      rw [ha, adjacentSwap, Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact Nat.add_right_comm (B.size ⟨j, by omega⟩)
        (B.size ⟨j + 2, h⟩) (B.size ⟨j + 1, by omega⟩)
  · change
      (∑ k : Fin (B.tripleInnerLength j m),
        B.size (B.adjacentSwap (j + δ) (by omega) (B.tripleBlockEquiv j h ⟨m, k⟩))) =
      ∑ k : Fin (B.tripleInnerLength j m), B.size (B.tripleBlockEquiv j h ⟨m, k⟩)
    apply Finset.sum_congr rfl
    intro k _
    rw [triple_swap_fixes_outside B j h δ hδ m hm k]

/-- Both local swaps give the literal same coarse triple-merged shape. -/
theorem tripleMerge_permute_adjacentSwap :
    (B.permute (B.adjacentSwap (j + δ) (by omega))).tripleMerge j h =
      B.tripleMerge j h :=
  ext_of_size rfl fun m => B.tripleMergeSize_permute_adjacentSwap j h δ hδ m

/-- The refinement for either swapped ordering, over the same coarse shape. -/
def tripleSwapRefinement : BlockRefinement (B.tripleMerge j h) := fun m =>
  { length := B.tripleInnerLength j m
    size := fun k => B.size (B.adjacentSwap (j + δ) (by omega)
      (B.tripleBlockEquiv j h ⟨m, k⟩))
    positive := fun _ => B.positive _
    sum_eq := B.tripleMergeSize_permute_adjacentSwap j h δ hδ m }

/-- Consecutive original positions for the swapped triple refinement. -/
def tripleSwapBlockEquiv :
    ((i : Fin (B.tripleMerge j h).length) ×
      Fin (B.tripleSwapRefinement j h δ hδ i).length) ≃ Fin B.length :=
  B.tripleBlockEquiv j h

@[simp] theorem tripleSwapBlockEquiv_apply
    (a : (i : Fin (B.tripleMerge j h).length) ×
      Fin (B.tripleSwapRefinement j h δ hδ i).length) :
    B.tripleSwapBlockEquiv j h δ hδ a = B.tripleBlockEquiv j h a := rfl

theorem tripleSwapRefinement_length (m : Fin (B.tripleMerge j h).length) :
    (B.tripleSwapRefinement j h δ hδ m).length =
      (B.tripleRefinement j h m).length := rfl

theorem tripleSwapRefinement_size_merged
    (k : Fin (B.tripleSwapRefinement j h δ hδ (B.tripleMergeIndex j h)).length) :
    (B.tripleSwapRefinement j h δ hδ (B.tripleMergeIndex j h)).size k =
      B.size (B.adjacentSwap (j + δ) (by omega)
        ⟨j + k.val, by
          have hk : k.val < 3 := (B.tripleRefinement_length_merged j h) ▸ k.isLt
          omega⟩) := by
  change B.size (B.adjacentSwap (j + δ) _
    (B.tripleBlockEquiv j h ⟨B.tripleMergeIndex j h, k⟩)) = _
  congr 1
  congr 1
  apply Fin.ext
  rw [tripleBlockEquiv_val]
  simp

theorem tripleSwapBlock_size
    (a : (i : Fin (B.tripleMerge j h).length) ×
      Fin (B.tripleSwapRefinement j h δ hδ i).length) :
    (B.tripleSwapRefinement j h δ hδ a.1).size a.2 =
      (B.permute (B.adjacentSwap (j + δ) (by omega))).size
        (B.tripleSwapBlockEquiv j h δ hδ a) := rfl

theorem tripleSwapBlockEquiv_lt_iff
    (a b : (i : Fin (B.tripleMerge j h).length) ×
      Fin (B.tripleSwapRefinement j h δ hδ i).length) :
    B.tripleSwapBlockEquiv j h δ hδ a < B.tripleSwapBlockEquiv j h δ hδ b ↔
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val) :=
  B.tripleBlockEquiv_lt_iff j h a b

/-- The standard coordinates of each swapped refinement agree exactly with
the corresponding permuted original shape. -/
theorem tripleSwap_index (i : Fin (B.tripleMerge j h).length)
    (k : Fin (B.tripleSwapRefinement j h δ hδ i).length)
    (x : Fin ((B.tripleSwapRefinement j h δ hδ i).size k)) :
    (B.tripleMerge j h).index i ((B.tripleSwapRefinement j h δ hδ i).index k x) =
      (B.permute (B.adjacentSwap (j + δ) (by omega))).index
        (B.tripleSwapBlockEquiv j h δ hδ ⟨i, k⟩)
        (Fin.cast (B.tripleSwapBlock_size j h δ hδ ⟨i, k⟩) x) :=
  index_index_eq_of_lex (B.permute (B.adjacentSwap (j + δ) (by omega)))
    (B.tripleMerge j h) (B.tripleSwapRefinement j h δ hδ)
    (B.tripleSwapBlockEquiv j h δ hδ) (B.tripleSwapBlock_size j h δ hδ)
    (fun a b hab => (B.tripleSwapBlockEquiv_lt_iff j h δ hδ a b).mpr hab) i k x

/-- Each outside singleton refinement is unchanged by either local swap. -/
theorem tripleSwapRefinement_of_ne (m : Fin (B.tripleMerge j h).length)
    (hm : m.val ≠ j) :
    B.tripleSwapRefinement j h δ hδ m = B.tripleRefinement j h m := by
  apply ext_of_size (B₁ := B.tripleSwapRefinement j h δ hδ m)
    (B₂ := B.tripleRefinement j h m) rfl
  intro k
  change B.size (B.adjacentSwap (j + δ) _ (B.tripleBlockEquiv j h ⟨m, k⟩)) =
    B.size (B.tripleBlockEquiv j h ⟨m, k⟩)
  rw [triple_swap_fixes_outside B j h δ hδ m hm k]

end Swap

end Triple

end Langlands.GeneralLinear.BlockShape
