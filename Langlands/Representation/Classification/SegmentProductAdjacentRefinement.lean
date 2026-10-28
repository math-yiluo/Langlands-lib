import Langlands.Representation.Classification.SegmentProductRefinement
import Langlands.Representation.Classification.SegmentProductPermutation
import Langlands.Representation.Induction.BlockEquivalence

/-! Actual adjacent inner data in the common merged outer product. -/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n) (j : ℕ) (h : j + 1 < B.length)

/-- The list of labels at the merged slot is the original adjacent pair. -/
theorem ofFn_adjacentBlockEquiv_merged {α : Type*} (f : Fin B.length → α) :
    List.ofFn (fun l => f (B.adjacentBlockEquiv j h
      ⟨B.adjacentMergeIndex j h, l⟩)) =
      [f ⟨j, by omega⟩, f ⟨j + 1, h⟩] := by
  rw [List.ofFn_congr (B.adjacentRefinement_length_merged j h)]
  simp only [List.ofFn_succ, List.ofFn_zero]
  have h0 : B.adjacentBlockEquiv j h
      ⟨B.adjacentMergeIndex j h, Fin.cast
        (B.adjacentRefinement_length_merged j h).symm 0⟩ = ⟨j, by omega⟩ := by
    apply Fin.ext
    rw [adjacentBlockEquiv_val]
    simp
  have h1 : B.adjacentBlockEquiv j h
      ⟨B.adjacentMergeIndex j h, Fin.cast
        (B.adjacentRefinement_length_merged j h).symm (Fin.succ 0)⟩ = ⟨j + 1, h⟩ := by
    apply Fin.ext
    rw [adjacentBlockEquiv_val]
    simp
  change [f (B.adjacentBlockEquiv j h _), f (B.adjacentBlockEquiv j h _)] = _
  rw [h0, h1]

/-- The adjacent transposition fixes every inner label outside the merged slot. -/
theorem adjacentSwap_adjacentBlockEquiv_of_ne
    (m : Fin (B.adjacentMerge j h).length) (hm : m.val ≠ j)
    (k : Fin (B.adjacentRefinement j h m).length) :
    B.adjacentSwap j h (B.adjacentBlockEquiv j h ⟨m, k⟩) =
      B.adjacentBlockEquiv j h ⟨m, k⟩ := by
  have hk : k.val < 1 := (B.adjacentRefinement_length_of_ne j h m hm) ▸ k.isLt
  have hv := B.adjacentBlockEquiv_val j h ⟨m, k⟩
  dsimp only at hv
  apply Equiv.swap_apply_of_ne_of_ne
  · rw [ne_eq, Fin.ext_iff, hv]
    dsimp only
    split_ifs <;> omega
  · rw [ne_eq, Fin.ext_iff, hv]
    dsimp only
    split_ifs <;> omega

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData.SegmentProductDatum

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  {n : ℕ} (d : SegmentProductDatum.{uV,uF} T n)

private theorem ofFn_swap_of_eq_two {L : ℕ} (hL : L = 2) {α : Type*}
    (f : Fin L → α) :
    List.ofFn (fun i => f (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ i)) =
      (List.ofFn f).reverse := by
  subst L
  simp only [List.ofFn_succ, List.ofFn_zero]
  change [f (Equiv.swap (0 : Fin 2) 1 0), f (Equiv.swap (0 : Fin 2) 1 1)] =
    [f 1, f 0]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- A two-block adjacent transposition reverses the complete actual block list. -/
theorem blockList_permute_adjacentSwap_of_length_two (hl : d.length = 2) :
    (d.permute (d.shape.adjacentSwap 0 (by change 1 < d.length; omega))).blockList =
      d.blockList.reverse :=
  ofFn_swap_of_eq_two hl d.blockAt

variable
  (j : ℕ) (h : j + 1 < d.length)

/-- The actual original blocks inside each component of the adjacent merge. -/
def adjacentDatum (k : Fin (d.shape.adjacentMerge j h).length) :
    SegmentProductDatum.{uV,uF} T ((d.shape.adjacentMerge j h).size k) :=
  d.refinementDatum (d.shape.adjacentMerge j h) (d.shape.adjacentRefinement j h)
    (d.shape.adjacentBlockEquiv j h) (d.shape.adjacentBlock_size j h) k

/-- The actual swapped blocks inside the same merged outer shape. -/
def adjacentSwappedDatum (k : Fin (d.shape.adjacentMerge j h).length) :
    SegmentProductDatum.{uV,uF} T ((d.shape.adjacentMerge j h).size k) :=
  (d.permute (d.shape.adjacentSwap j h)).refinementDatum
    (d.shape.adjacentMerge j h) (d.shape.adjacentSwapRefinement j h)
    (d.shape.adjacentSwapBlockEquiv j h) (d.shape.adjacentSwapBlock_size j h) k

@[simp]
theorem adjacentDatum_blockList (k : Fin (d.shape.adjacentMerge j h).length) :
    (d.adjacentDatum j h k).blockList =
      List.ofFn (fun l => d.blockAt (d.shape.adjacentBlockEquiv j h ⟨k,l⟩)) := rfl

@[simp]
theorem adjacentSwappedDatum_blockList (k : Fin (d.shape.adjacentMerge j h).length) :
    (d.adjacentSwappedDatum j h k).blockList =
      List.ofFn (fun l => d.blockAt
        (d.shape.adjacentSwap j h (d.shape.adjacentBlockEquiv j h ⟨k,l⟩))) := rfl

/-- At the merged slot the actual original pair occurs in its original order. -/
theorem adjacentDatum_merged_blockList :
    (d.adjacentDatum j h (d.shape.adjacentMergeIndex j h)).blockList =
      [d.blockAt ⟨j, by omega⟩, d.blockAt ⟨j + 1, h⟩] := by
  exact d.shape.ofFn_adjacentBlockEquiv_merged j h d.blockAt

/-- At the merged slot the swapped actual pair occurs in reverse order. -/
theorem adjacentSwappedDatum_merged_blockList :
    (d.adjacentSwappedDatum j h (d.shape.adjacentMergeIndex j h)).blockList =
      [d.blockAt ⟨j + 1, h⟩, d.blockAt ⟨j, by omega⟩] := by
  rw [adjacentSwappedDatum_blockList,
    d.shape.ofFn_adjacentBlockEquiv_merged j h
      (fun l => d.blockAt (d.shape.adjacentSwap j h l))]
  dsimp only [BlockShape.adjacentSwap]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rfl

@[simp]
theorem adjacentDatum_merged_length :
    (d.adjacentDatum j h (d.shape.adjacentMergeIndex j h)).length = 2 :=
  d.shape.adjacentRefinement_length_merged j h

/-- The refinement retains the strong socle property of every supplied block. -/
theorem adjacentDatum_hasSegmentSocles (hd : d.HasSegmentSocles)
    (k : Fin (d.shape.adjacentMerge j h).length) :
    (d.adjacentDatum j h k).HasSegmentSocles :=
  fun l => hd (d.shape.adjacentBlockEquiv j h ⟨k,l⟩)

/-- The segments at the merged slot are exactly the original adjacent pair. -/
theorem adjacentDatum_merged_segments :
    List.ofFn (d.adjacentDatum j h (d.shape.adjacentMergeIndex j h)).segments =
      [d.segments ⟨j, by omega⟩, d.segments ⟨j + 1, h⟩] := by
  rw [← blockList_segments, adjacentDatum_merged_blockList]
  rfl

/-- The swapped merged datum is the actual adjacent transposition of the inner pair. -/
theorem adjacentSwappedDatum_merged_eq :
    d.adjacentSwappedDatum j h (d.shape.adjacentMergeIndex j h) =
      (d.adjacentDatum j h (d.shape.adjacentMergeIndex j h)).permute
        ((d.adjacentDatum j h (d.shape.adjacentMergeIndex j h)).shape.adjacentSwap 0
          (by
            change 1 < (d.adjacentDatum j h (d.shape.adjacentMergeIndex j h)).length
            rw [adjacentDatum_merged_length]
            decide)) := by
  apply blockList_injective
  rw [blockList_permute_adjacentSwap_of_length_two _
    (d.adjacentDatum_merged_length j h), adjacentDatum_merged_blockList,
    adjacentSwappedDatum_merged_blockList]
  rfl

/-- Each outside inner datum, including its actual representation, is unchanged. -/
theorem adjacentSwappedDatum_of_ne
    (k : Fin (d.shape.adjacentMerge j h).length) (hk : k.val ≠ j) :
    d.adjacentSwappedDatum j h k = d.adjacentDatum j h k := by
  apply blockList_injective
  rw [adjacentSwappedDatum_blockList, adjacentDatum_blockList]
  apply congrArg List.ofFn
  funext l
  rw [BlockShape.adjacentSwap_adjacentBlockEquiv_of_ne _ _ _ _ hk]

/-- Regroup the original product into the actual adjacent inner data. -/
def adjacentInducedEquiv :
    letI := T.topology
    d.induced.representation.Equiv
      (T.normalizedProductInduced (d.shape.adjacentMerge j h)
        (fun k => (d.adjacentDatum j h k).induced.representation)) := by
  letI := T.topology
  exact d.refinementInducedEquiv _ _ _ _ (d.shape.adjacent_index j h)

/-- Regroup the swapped product into the common outer shape and actual swapped data. -/
def adjacentSwappedInducedEquiv :
    letI := T.topology
    (d.permute (d.shape.adjacentSwap j h)).induced.representation.Equiv
      (T.normalizedProductInduced (d.shape.adjacentMerge j h)
        (fun k => (d.adjacentSwappedDatum j h k).induced.representation)) := by
  letI := T.topology
  exact (d.permute (d.shape.adjacentSwap j h)).refinementInducedEquiv
    _ _ _ _ (d.shape.adjacentSwap_index j h)

/-- Lift a supplied equivalence of the actual merged pair to the full product. -/
def adjacentSwapInducedEquiv
    (e : letI := T.topology
      (d.adjacentDatum j h (d.shape.adjacentMergeIndex j h)).induced.representation.Equiv
        (d.adjacentSwappedDatum j h (d.shape.adjacentMergeIndex j h)).induced.representation) :
    letI := T.topology
    d.induced.representation.Equiv
      (d.permute (d.shape.adjacentSwap j h)).induced.representation := by
  letI := T.topology
  let a : ∀ k, (d.adjacentDatum j h k).induced.representation.Equiv
      (d.adjacentSwappedDatum j h k).induced.representation := by
    intro k
    by_cases hk : k = d.shape.adjacentMergeIndex j h
    · subst k
      exact e
    · have hval : k.val ≠ j := by
        intro he
        exact hk (Fin.ext he)
      exact inducedEquivOfBlockListEq _ _ (congrArg blockList
        (d.adjacentSwappedDatum_of_ne j h k hval).symm)
  exact (d.adjacentInducedEquiv j h).trans
    ((T.normalizedProductInducedEquiv (d.shape.adjacentMerge j h) a).trans
      (d.adjacentSwappedInducedEquiv j h).symm)

end Langlands.PadicField.TopologicalData.SegmentProductDatum
