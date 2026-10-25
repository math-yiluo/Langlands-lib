import Langlands.Group.GL.SingleBlock
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Langlands.Representation.CuspidalSupport.BlockPermutation

/-!
# Merging two adjacent blocks

For an ordered block shape `B` and adjacent slots `j`, `j + 1`, this module constructs
the shape obtained by merging those two blocks, its inner refinement recovering `B`,
the consecutive label bijection, and the exact standard-coordinate identity. It also
compares the shape whose two merged blocks are swapped.
-/

namespace Langlands.GeneralLinear.BlockShape

open Geometric

variable {n : ℕ}

/-- Two block shapes of the same rank are equal once their lengths and sizes agree. -/
theorem ext_of_size {B₁ B₂ : BlockShape n} (hl : B₁.length = B₂.length)
    (hs : ∀ i, B₁.size i = B₂.size (Fin.cast hl i)) : B₁ = B₂ := by
  rcases B₁ with ⟨l, s₁, p₁, e₁⟩
  rcases B₂ with ⟨l₂, s₂, p₂, e₂⟩
  dsimp only at hl hs
  subst hl
  have hs' : s₁ = s₂ := funext fun i => hs i
  subst hs'
  rfl

section Coordinates

variable (B D : BlockShape n) (S : BlockRefinement D)
    (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
    (hs : ∀ a, (S a.1).size a.2 = B.size (e a))

/-- A size-compatible label bijection which increases for the lexicographic order of
outer and inner labels gives the exact standard-coordinate identity. -/
theorem index_index_eq_of_lex
    (he : ∀ a b : (i : Fin D.length) × Fin (S i).length,
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val) → e a < e b)
    (i : Fin D.length) (k : Fin (S i).length) (x : Fin ((S i).size k)) :
    D.index i ((S i).index k x) = B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x) := by
  let ψ : (i : Fin D.length) → (S i).Index → Fin n := fun i q =>
    B.index (e ⟨i, q.1⟩) (Fin.cast (hs ⟨i, q.1⟩) q.2)
  let φ : D.Index → Fin n := fun p => ψ p.1 ((S p.1).indexEquiv.symm p.2)
  let H : Fin n → Fin n := fun a => φ (D.indexEquiv.symm a)
  have hH : ∀ (i : Fin D.length) (k : Fin (S i).length) (x : Fin ((S i).size k)),
      H (D.index i ((S i).index k x)) = B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x) := by
    intro i k x
    change φ (D.indexEquiv.symm (D.indexEquiv ⟨i, (S i).indexEquiv ⟨k, x⟩⟩)) = _
    rw [Equiv.symm_apply_apply]
    change ψ i ((S i).indexEquiv.symm ((S i).indexEquiv ⟨k, x⟩)) = _
    rw [Equiv.symm_apply_apply]
  have hmono : StrictMono H := by
    intro a a' haa'
    obtain ⟨⟨i, y⟩, rfl⟩ := D.indexEquiv.surjective a
    obtain ⟨⟨i', y'⟩, rfl⟩ := D.indexEquiv.surjective a'
    obtain ⟨⟨k, x⟩, rfl⟩ := (S i).indexEquiv.surjective y
    obtain ⟨⟨k', x'⟩, rfl⟩ := (S i').indexEquiv.surjective y'
    change D.index i ((S i).index k x) < D.index i' ((S i').index k' x') at haa'
    change H (D.index i ((S i).index k x)) < H (D.index i' ((S i').index k' x'))
    rw [hH, hH]
    have hii : i ≤ i' := by
      simpa only [blockIndex_index] using blockIndex_monotone D haa'.le
    rcases hii.lt_or_eq with hii | rfl
    · exact B.index_lt_index_of_block_lt (he ⟨i, k⟩ ⟨i', k'⟩ (Or.inl hii)) _ _
    · have hy := (index_strictMono D i).lt_iff_lt.mp haa'
      have hkk : k ≤ k' := by
        simpa only [blockIndex_index] using blockIndex_monotone (S i) hy.le
      rcases hkk.lt_or_eq with hkk | rfl
      · exact B.index_lt_index_of_block_lt
          (he ⟨i, k⟩ ⟨i, k'⟩ (Or.inr ⟨rfl, Fin.lt_def.mp hkk⟩)) _ _
      · have hxx := (index_strictMono (S i) k).lt_iff_lt.mp hy
        exact index_strictMono B _ hxx
  rw [← hH]
  exact (le_antisymm hmono.apply_le hmono.le_apply).symm

end Coordinates

private theorem sum_fin_of_eq_two (L : ℕ) (hL : L = 2) (f : Fin L → ℕ) :
    ∑ k, f k = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  subst hL
  exact Fin.sum_univ_two f

private theorem sum_fin_of_eq_one (L : ℕ) (hL : L = 1) (f : Fin L → ℕ) :
    ∑ k, f k = f ⟨0, by omega⟩ := by
  subst hL
  exact Fin.sum_univ_one f

section Merge

variable (B : BlockShape n) (j : ℕ) (h : j + 1 < B.length)

/-- The number of original blocks in each merged block: two at slot `j`, one elsewhere. -/
def adjacentInnerLength (m : Fin (B.length - 1)) : ℕ := if m.val = j then 2 else 1

private theorem sum_range_adjacent (m : ℕ) :
    ∑ i ∈ Finset.range m, (if i = j then 2 else 1) = m + if j < m then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

private theorem sum_adjacentInnerLength_castLE (m : ℕ) (hm : m ≤ B.length - 1) :
    ∑ i : Fin m, B.adjacentInnerLength j (Fin.castLE hm i) = m + if j < m then 1 else 0 :=
  (Fin.sum_univ_eq_sum_range (fun i => if i = j then 2 else 1) m).trans
    (sum_range_adjacent j m)

include h in
/-- The inner block counts add up to the original number of blocks. -/
theorem sum_adjacentInnerLength : ∑ m, B.adjacentInnerLength j m = B.length := by
  calc ∑ m, B.adjacentInnerLength j m
      = ∑ i ∈ Finset.range (B.length - 1), (if i = j then 2 else 1) :=
        Fin.sum_univ_eq_sum_range (fun i => if i = j then 2 else 1) _
    _ = B.length := by
        rw [sum_range_adjacent, ite_eq_left (by omega)]
        omega

/-- Consecutive numbering of the outer and inner labels; it is the original numbering. -/
def adjacentLabelEquiv :
    ((m : Fin (B.length - 1)) × Fin (B.adjacentInnerLength j m)) ≃ Fin B.length :=
  finSigmaFinEquiv.trans (finCongr (B.sum_adjacentInnerLength j h))

theorem adjacentLabelEquiv_val
    (q : (m : Fin (B.length - 1)) × Fin (B.adjacentInnerLength j m)) :
    ((B.adjacentLabelEquiv j h q : Fin B.length) : ℕ) =
      q.1.val + q.2.val + if j < q.1.val then 1 else 0 := by
  rw [adjacentLabelEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply, B.sum_adjacentInnerLength_castLE j]
  omega

/-- Block sizes after merging slots `j` and `j + 1`. -/
def adjacentMergeSize (m : Fin (B.length - 1)) : ℕ :=
  if m.val < j then B.size ⟨m.val, by have := m.isLt; omega⟩
  else if m.val = j then B.size ⟨j, by omega⟩ + B.size ⟨j + 1, h⟩
  else B.size ⟨m.val + 1, by have := m.isLt; omega⟩

theorem adjacentMergeSize_pos (m : Fin (B.length - 1)) : 0 < B.adjacentMergeSize j h m := by
  unfold adjacentMergeSize
  split_ifs
  · exact B.positive _
  · exact Nat.lt_of_lt_of_le (B.positive _) (Nat.le_add_right _ _)
  · exact B.positive _

/-- Each merged size is the total size of the original blocks it contains. -/
theorem adjacentMergeSize_eq_sum (m : Fin (B.length - 1)) :
    B.adjacentMergeSize j h m =
      ∑ k : Fin (B.adjacentInnerLength j m), B.size (B.adjacentLabelEquiv j h ⟨m, k⟩) := by
  rcases m with ⟨m, hm'⟩
  by_cases hm : m = j
  · rw [sum_fin_of_eq_two (B.adjacentInnerLength j ⟨m, hm'⟩) (ite_eq_left hm)]
    unfold adjacentMergeSize
    dsimp only
    rw [ite_eq_right (by omega), ite_eq_left hm]
    congr 1 <;> congr 1 <;> apply Fin.ext <;> rw [adjacentLabelEquiv_val] <;> dsimp only <;>
      split_ifs <;> omega
  · rw [sum_fin_of_eq_one (B.adjacentInnerLength j ⟨m, hm'⟩) (ite_eq_right hm)]
    unfold adjacentMergeSize
    dsimp only
    rw [ite_eq_right hm]
    split_ifs <;>
    · congr 1
      apply Fin.ext
      rw [adjacentLabelEquiv_val]
      dsimp only
      split_ifs <;> omega

/-- The ordered shape obtained by merging blocks `j` and `j + 1` of `B`. -/
def adjacentMerge : BlockShape n where
  length := B.length - 1
  size := B.adjacentMergeSize j h
  positive := B.adjacentMergeSize_pos j h
  sum_eq := by
    calc ∑ m, B.adjacentMergeSize j h m
        = ∑ m, ∑ k : Fin (B.adjacentInnerLength j m),
            B.size (B.adjacentLabelEquiv j h ⟨m, k⟩) :=
          Finset.sum_congr rfl fun m _ => B.adjacentMergeSize_eq_sum j h m
      _ = ∑ q, B.size (B.adjacentLabelEquiv j h q) :=
          (Fintype.sum_sigma fun q => B.size (B.adjacentLabelEquiv j h q)).symm
      _ = ∑ b, B.size b := Equiv.sum_comp _ _
      _ = n := B.sum_eq

/-- Inside each merged block, the original blocks it contains, in their original order. -/
def adjacentRefinement : BlockRefinement (B.adjacentMerge j h) := fun m =>
  { length := B.adjacentInnerLength j m
    size := fun k => B.size (B.adjacentLabelEquiv j h ⟨m, k⟩)
    positive := fun _ => B.positive _
    sum_eq := (B.adjacentMergeSize_eq_sum j h m).symm }

/-- The outer/inner labels of the adjacent refinement and the original block labels. -/
def adjacentBlockEquiv :
    ((i : Fin (B.adjacentMerge j h).length) × Fin (B.adjacentRefinement j h i).length) ≃
      Fin B.length :=
  B.adjacentLabelEquiv j h

/-- Every inner block has the size of its original block. -/
theorem adjacentBlock_size
    (a : (i : Fin (B.adjacentMerge j h).length) × Fin (B.adjacentRefinement j h i).length) :
    (B.adjacentRefinement j h a.1).size a.2 = B.size (B.adjacentBlockEquiv j h a) := rfl

/-- Explicit value of the label bijection. -/
theorem adjacentBlockEquiv_val
    (a : (i : Fin (B.adjacentMerge j h).length) × Fin (B.adjacentRefinement j h i).length) :
    ((B.adjacentBlockEquiv j h a : Fin B.length) : ℕ) =
      a.1.val + a.2.val + if j < a.1.val then 1 else 0 :=
  B.adjacentLabelEquiv_val j h a

/-- The label bijection is exactly the lexicographic order of outer and inner labels. -/
theorem adjacentBlockEquiv_lt_iff
    (a b : (i : Fin (B.adjacentMerge j h).length) × Fin (B.adjacentRefinement j h i).length) :
    B.adjacentBlockEquiv j h a < B.adjacentBlockEquiv j h b ↔
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val) := by
  rcases a with ⟨⟨m, hm⟩, k⟩
  rcases b with ⟨⟨m', hm'⟩, k'⟩
  have hk : k.val < if m = j then 2 else 1 := k.isLt
  have hk' : k'.val < if m' = j then 2 else 1 := k'.isLt
  rw [Fin.lt_def, adjacentBlockEquiv_val, adjacentBlockEquiv_val, Fin.lt_def, Fin.ext_iff]
  dsimp only
  split_ifs at hk hk' ⊢ <;> omega

/-- The exact standard-coordinate identity of the adjacent refinement. -/
theorem adjacent_index (i : Fin (B.adjacentMerge j h).length)
    (k : Fin (B.adjacentRefinement j h i).length)
    (x : Fin ((B.adjacentRefinement j h i).size k)) :
    (B.adjacentMerge j h).index i ((B.adjacentRefinement j h i).index k x) =
      B.index (B.adjacentBlockEquiv j h ⟨i, k⟩)
        (Fin.cast (B.adjacentBlock_size j h ⟨i, k⟩) x) :=
  index_index_eq_of_lex B (B.adjacentMerge j h) (B.adjacentRefinement j h)
    (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h)
    (fun a b hab => (B.adjacentBlockEquiv_lt_iff j h a b).mpr hab) i k x

/-! ### Explicit length and size laws -/

@[simp] theorem adjacentMerge_length : (B.adjacentMerge j h).length = B.length - 1 := rfl

/-- The merged slot. -/
def adjacentMergeIndex : Fin (B.adjacentMerge j h).length :=
  ⟨j, by change j < B.length - 1; omega⟩

@[simp] theorem adjacentMergeIndex_val : (B.adjacentMergeIndex j h).val = j := rfl

theorem adjacentMerge_size_of_lt (m : Fin (B.adjacentMerge j h).length) (hm : m.val < j) :
    (B.adjacentMerge j h).size m = B.size ⟨m.val, by omega⟩ := by
  rcases m with ⟨m, hm'⟩
  dsimp only at hm
  change B.adjacentMergeSize j h ⟨m, hm'⟩ = _
  unfold adjacentMergeSize
  dsimp only
  rw [ite_eq_left hm]

theorem adjacentMerge_size_merged :
    (B.adjacentMerge j h).size (B.adjacentMergeIndex j h) =
      B.size ⟨j, by omega⟩ + B.size ⟨j + 1, h⟩ := by
  change B.adjacentMergeSize j h ⟨j, _⟩ = _
  unfold adjacentMergeSize
  rw [ite_eq_right (lt_irrefl j), ite_eq_left rfl]

theorem adjacentMerge_size_of_gt (m : Fin (B.adjacentMerge j h).length) (hm : j < m.val) :
    (B.adjacentMerge j h).size m =
      B.size ⟨m.val + 1, by have : m.val < B.length - 1 := m.isLt; omega⟩ := by
  rcases m with ⟨m, hm'⟩
  dsimp only at hm
  change B.adjacentMergeSize j h ⟨m, hm'⟩ = _
  unfold adjacentMergeSize
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem adjacentRefinement_length (m : Fin (B.adjacentMerge j h).length) :
    (B.adjacentRefinement j h m).length = if m.val = j then 2 else 1 := rfl

theorem adjacentRefinement_length_merged :
    (B.adjacentRefinement j h (B.adjacentMergeIndex j h)).length = 2 := ite_eq_left rfl

theorem adjacentRefinement_length_of_ne (m : Fin (B.adjacentMerge j h).length)
    (hm : m.val ≠ j) : (B.adjacentRefinement j h m).length = 1 := ite_eq_right hm

/-- The total number of inner blocks is the original number of blocks. -/
theorem adjacentRefinement_total_length :
    ∑ m, (B.adjacentRefinement j h m).length = B.length :=
  B.sum_adjacentInnerLength j h

/-- Inner block `k` of merged block `m` is original block `m + k`, shifted once after
the merged slot. -/
theorem adjacentRefinement_size (m : Fin (B.adjacentMerge j h).length)
    (k : Fin (B.adjacentRefinement j h m).length) :
    (B.adjacentRefinement j h m).size k =
      B.size ⟨m.val + k.val + if j < m.val then 1 else 0,
        by rw [← B.adjacentBlockEquiv_val j h ⟨m, k⟩]; exact Fin.isLt _⟩ :=
  congrArg B.size (Fin.ext (B.adjacentBlockEquiv_val j h ⟨m, k⟩))

/-- At the merged slot, the two inner blocks are the original blocks `j` and `j + 1`,
in this order. -/
theorem adjacentRefinement_size_merged (k : Fin (B.adjacentRefinement j h
    (B.adjacentMergeIndex j h)).length) :
    (B.adjacentRefinement j h (B.adjacentMergeIndex j h)).size k =
      B.size ⟨j + k.val, by
        have := k.isLt
        have := B.adjacentRefinement_length_merged j h
        omega⟩ := by
  rw [adjacentRefinement_size]
  congr 2
  simp

/-- Away from the merged slot, the unique inner block is the whole merged block. -/
theorem adjacentRefinement_size_of_ne (m : Fin (B.adjacentMerge j h).length)
    (hm : m.val ≠ j) (k : Fin (B.adjacentRefinement j h m).length) :
    (B.adjacentRefinement j h m).size k = (B.adjacentMerge j h).size m := by
  have hsum := (B.adjacentRefinement j h m).sum_eq
  rw [Finset.sum_eq_single k] at hsum
  · exact hsum
  · intro k' _ hk'
    have h₁ := k.isLt
    have h₂ := k'.isLt
    have hl := B.adjacentRefinement_length_of_ne j h m hm
    exact absurd (Fin.ext (by omega)) hk'
  · simp

/-! ### The collapse of block labels -/

/-- The merged block containing each original block. -/
def adjacentCollapse (b : Fin B.length) : Fin (B.adjacentMerge j h).length :=
  ⟨if b.val ≤ j then b.val else b.val - 1, by
    change _ < B.length - 1
    have := b.isLt
    split_ifs <;> omega⟩

theorem adjacentCollapse_val (b : Fin B.length) :
    (B.adjacentCollapse j h b).val = if b.val ≤ j then b.val else b.val - 1 := rfl

/-- The collapse sends each original label to its outer label. -/
theorem adjacentCollapse_adjacentBlockEquiv
    (a : (i : Fin (B.adjacentMerge j h).length) × Fin (B.adjacentRefinement j h i).length) :
    B.adjacentCollapse j h (B.adjacentBlockEquiv j h a) = a.1 := by
  rcases a with ⟨⟨m, hm⟩, k⟩
  have hk : k.val < if m = j then 2 else 1 := k.isLt
  apply Fin.ext
  rw [adjacentCollapse_val, adjacentBlockEquiv_val]
  dsimp only
  split_ifs at hk ⊢ <;> omega

theorem adjacentBlockEquiv_symm_fst (b : Fin B.length) :
    ((B.adjacentBlockEquiv j h).symm b).1 = B.adjacentCollapse j h b := by
  conv_rhs => rw [← (B.adjacentBlockEquiv j h).apply_symm_apply b]
  rw [adjacentCollapse_adjacentBlockEquiv]

/-- Two original blocks have the same merged block exactly when they are equal or are
the two merged slots. -/
theorem adjacentCollapse_eq_iff (b b' : Fin B.length) :
    B.adjacentCollapse j h b = B.adjacentCollapse j h b' ↔
      b = b' ∨ (b.val = j ∧ b'.val = j + 1) ∨ (b.val = j + 1 ∧ b'.val = j) := by
  rw [Fin.ext_iff, Fin.ext_iff, adjacentCollapse_val, adjacentCollapse_val]
  split_ifs <;> omega

theorem adjacentCollapse_monotone : Monotone (B.adjacentCollapse j h) := by
  intro b b' hb
  rw [Fin.le_def] at hb ⊢
  rw [adjacentCollapse_val, adjacentCollapse_val]
  split_ifs <;> omega

theorem adjacentCollapse_surjective : Function.Surjective (B.adjacentCollapse j h) := by
  intro m
  obtain ⟨k, hk⟩ : ∃ k : Fin (B.adjacentRefinement j h m).length, True :=
    ⟨⟨0, by rw [adjacentRefinement_length]; split_ifs <;> omega⟩, trivial⟩
  exact ⟨B.adjacentBlockEquiv j h ⟨m, k⟩, B.adjacentCollapse_adjacentBlockEquiv j h ⟨m, k⟩⟩

/-- The merged block of an original coordinate is the collapse of its original block. -/
theorem blockIndex_adjacentMerge_index (b : Fin B.length) (x : Fin (B.size b)) :
    blockIndex (B.adjacentMerge j h) (B.index b x) = B.adjacentCollapse j h b := by
  obtain ⟨a, rfl⟩ := (B.adjacentBlockEquiv j h).surjective b
  rw [B.adjacentCollapse_adjacentBlockEquiv j h a]
  have hx : B.index (B.adjacentBlockEquiv j h a) x =
      (B.adjacentMerge j h).index a.1 ((B.adjacentRefinement j h a.1).index a.2
        (Fin.cast (B.adjacentBlock_size j h a).symm x)) :=
    (B.adjacent_index j h a.1 a.2 _).symm
  rw [hx, blockIndex_index]

theorem blockIndex_adjacentMerge (x : Fin n) :
    blockIndex (B.adjacentMerge j h) x = B.adjacentCollapse j h (blockIndex B x) := by
  obtain ⟨⟨b, y⟩, rfl⟩ := B.indexEquiv.surjective x
  change blockIndex (B.adjacentMerge j h) (B.index b y) =
    B.adjacentCollapse j h (blockIndex B (B.index b y))
  rw [blockIndex_index, blockIndex_adjacentMerge_index]

/-- The same compatibility, stated with the standard numberings. -/
theorem adjacentMerge_indexEquiv_symm_fst (p : B.Index) :
    ((B.adjacentMerge j h).indexEquiv.symm (B.indexEquiv p)).1 =
      B.adjacentCollapse j h p.1 :=
  B.blockIndex_adjacentMerge_index j h p.1 p.2

end Merge

section Swap

variable (B : BlockShape n) (j : ℕ) (h : j + 1 < B.length)

/-- The transposition of the adjacent block labels `j` and `j + 1`. -/
def adjacentSwap : Equiv.Perm (Fin B.length) := Equiv.swap ⟨j, by omega⟩ ⟨j + 1, h⟩

theorem adjacentMergeSize_permute_adjacentSwap (m : Fin (B.length - 1)) :
    (B.permute (B.adjacentSwap j h)).adjacentMergeSize j h m = B.adjacentMergeSize j h m := by
  rcases m with ⟨m, hm⟩
  unfold adjacentMergeSize
  dsimp only
  split_ifs with h₁ h₂
  · change B.size (B.adjacentSwap j h ⟨m, _⟩) = _
    rw [adjacentSwap, Equiv.swap_apply_of_ne_of_ne] <;> simp only [ne_eq, Fin.ext_iff] <;>
      omega
  · change B.size (B.adjacentSwap j h ⟨j, _⟩) + B.size (B.adjacentSwap j h ⟨j + 1, h⟩) = _
    rw [adjacentSwap, Equiv.swap_apply_left, Equiv.swap_apply_right, Nat.add_comm]
  · change B.size (B.adjacentSwap j h ⟨m + 1, _⟩) = _
    rw [adjacentSwap, Equiv.swap_apply_of_ne_of_ne] <;> simp only [ne_eq, Fin.ext_iff] <;>
      omega

/-- Merging the same adjacent slots of the swapped shape gives the same merged shape. -/
theorem adjacentMerge_permute_adjacentSwap :
    (B.permute (B.adjacentSwap j h)).adjacentMerge j h = B.adjacentMerge j h :=
  ext_of_size rfl fun m => B.adjacentMergeSize_permute_adjacentSwap j h m

/-- The refinement of the swapped shape, placed in the common merged shape. -/
def adjacentSwapRefinement : BlockRefinement (B.adjacentMerge j h) := fun m =>
  ((B.permute (B.adjacentSwap j h)).adjacentRefinement j h m).rankCast
    (B.adjacentMergeSize_permute_adjacentSwap j h m)

/-- Its labels, numbered consecutively, are the block labels of the swapped shape. -/
def adjacentSwapBlockEquiv :
    ((i : Fin (B.adjacentMerge j h).length) × Fin (B.adjacentSwapRefinement j h i).length) ≃
      Fin (B.permute (B.adjacentSwap j h)).length :=
  (B.permute (B.adjacentSwap j h)).adjacentBlockEquiv j h

/-- The swapped labels occupy the same consecutive positions as the original labels. -/
theorem adjacentSwapBlockEquiv_apply
    (a : (i : Fin (B.adjacentMerge j h).length) × Fin (B.adjacentSwapRefinement j h i).length) :
    (B.adjacentSwapBlockEquiv j h a : Fin B.length) = B.adjacentBlockEquiv j h a := rfl

theorem adjacentSwapBlock_size
    (a : (i : Fin (B.adjacentMerge j h).length) × Fin (B.adjacentSwapRefinement j h i).length) :
    (B.adjacentSwapRefinement j h a.1).size a.2 =
      (B.permute (B.adjacentSwap j h)).size (B.adjacentSwapBlockEquiv j h a) := rfl

theorem adjacentSwapBlockEquiv_lt_iff
    (a b : (i : Fin (B.adjacentMerge j h).length) × Fin (B.adjacentSwapRefinement j h i).length) :
    B.adjacentSwapBlockEquiv j h a < B.adjacentSwapBlockEquiv j h b ↔
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val) :=
  (B.permute (B.adjacentSwap j h)).adjacentBlockEquiv_lt_iff j h a b

/-- The exact standard-coordinate identity of the swapped shape in the common merged
shape. -/
theorem adjacentSwap_index (i : Fin (B.adjacentMerge j h).length)
    (k : Fin (B.adjacentSwapRefinement j h i).length)
    (x : Fin ((B.adjacentSwapRefinement j h i).size k)) :
    (B.adjacentMerge j h).index i ((B.adjacentSwapRefinement j h i).index k x) =
      (B.permute (B.adjacentSwap j h)).index (B.adjacentSwapBlockEquiv j h ⟨i, k⟩)
        (Fin.cast (B.adjacentSwapBlock_size j h ⟨i, k⟩) x) :=
  index_index_eq_of_lex (B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h)
    (B.adjacentSwapRefinement j h) (B.adjacentSwapBlockEquiv j h)
    (B.adjacentSwapBlock_size j h)
    (fun a b hab => (B.adjacentSwapBlockEquiv_lt_iff j h a b).mpr hab) i k x

theorem adjacentSwapRefinement_length (m : Fin (B.adjacentMerge j h).length) :
    (B.adjacentSwapRefinement j h m).length = (B.adjacentRefinement j h m).length := rfl

/-- At the merged slot, the swapped refinement has the original blocks `j + 1` and `j`,
in this order. -/
theorem adjacentSwapRefinement_size_merged (k : Fin (B.adjacentSwapRefinement j h
    (B.adjacentMergeIndex j h)).length) :
    (B.adjacentSwapRefinement j h (B.adjacentMergeIndex j h)).size k =
      B.size ⟨j + 1 - k.val, by omega⟩ := by
  have hk : k.val < 2 := (B.adjacentRefinement_length_merged j h) ▸ k.isLt
  change B.size (B.adjacentSwap j h (B.adjacentBlockEquiv j h ⟨_, k⟩)) = _
  congr 1
  have hv : (B.adjacentBlockEquiv j h ⟨B.adjacentMergeIndex j h, k⟩).val = j + k.val := by
    rw [adjacentBlockEquiv_val]
    simp
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk0 | hk1
  · have hk0 : k.val = 0 := by omega
    have he : B.adjacentBlockEquiv j h ⟨B.adjacentMergeIndex j h, k⟩ = ⟨j, by omega⟩ :=
      Fin.ext (by rw [hv, hk0]; rfl)
    rw [he, adjacentSwap, Equiv.swap_apply_left]
    apply Fin.ext
    simp [hk0]
  · have he : B.adjacentBlockEquiv j h ⟨B.adjacentMergeIndex j h, k⟩ = ⟨j + 1, h⟩ :=
      Fin.ext (by rw [hv, hk1])
    rw [he, adjacentSwap, Equiv.swap_apply_right]
    apply Fin.ext
    simp [hk1]

/-- The two inner sizes at the merged slot are reversed. -/
theorem adjacentSwapRefinement_size_merged_rev (k : Fin (B.adjacentSwapRefinement j h
    (B.adjacentMergeIndex j h)).length) :
    (B.adjacentSwapRefinement j h (B.adjacentMergeIndex j h)).size k =
      (B.adjacentRefinement j h (B.adjacentMergeIndex j h)).size
        ⟨1 - k.val, by rw [adjacentRefinement_length_merged]; omega⟩ := by
  have hk : k.val < 2 := (B.adjacentRefinement_length_merged j h) ▸ k.isLt
  rw [adjacentSwapRefinement_size_merged, adjacentRefinement_size_merged]
  congr 2
  dsimp only
  omega

/-- Away from the merged slot, the one-block components are unchanged. -/
theorem adjacentSwapRefinement_of_ne (m : Fin (B.adjacentMerge j h).length)
    (hm : m.val ≠ j) :
    B.adjacentSwapRefinement j h m = B.adjacentRefinement j h m := by
  refine ext_of_size (B₁ := B.adjacentSwapRefinement j h m)
    (B₂ := B.adjacentRefinement j h m) rfl fun k => ?_
  change B.size (B.adjacentSwap j h (B.adjacentBlockEquiv j h ⟨m, k⟩)) =
    B.size (B.adjacentBlockEquiv j h ⟨m, k⟩)
  have hk : k.val < 1 := (B.adjacentRefinement_length_of_ne j h m hm) ▸ k.isLt
  have hv := B.adjacentBlockEquiv_val j h ⟨m, k⟩
  dsimp only at hv
  congr 1
  apply Equiv.swap_apply_of_ne_of_ne
  · rw [ne_eq, Fin.ext_iff, hv]
    dsimp only
    split_ifs <;> omega
  · rw [ne_eq, Fin.ext_iff, hv]
    dsimp only
    split_ifs <;> omega

/-- The swapped refinement is the refinement of the swapped shape, transported to the
common merged block sizes. -/
theorem adjacentSwapRefinement_apply (m : Fin (B.adjacentMerge j h).length) :
    B.adjacentSwapRefinement j h m =
      ((B.permute (B.adjacentSwap j h)).adjacentRefinement j h m).rankCast
        (B.adjacentMergeSize_permute_adjacentSwap j h m) := rfl

end Swap

end Langlands.GeneralLinear.BlockShape
