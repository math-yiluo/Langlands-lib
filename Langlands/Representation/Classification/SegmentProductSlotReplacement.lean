import Langlands.Representation.Classification.SegmentProductAdjacentRefinement
import Langlands.Representation.Classification.SegmentProductConcatenation

/-! Replacement of an actual adjacent pair by arbitrary data of the same rank. -/

noncomputable section

namespace Langlands.FiniteConcatenation

/-- Singleton fibers outside one merged slot give the exact take/drop formula. -/
theorem flatten_ofFn_adjacent {α : Type*} {N : ℕ} (j : ℕ) (h : j + 1 < N)
    (f : Fin N → α) (g : Fin (N - 1) → List α)
    (hl : ∀ k (hk : k.val < j), g k = [f ⟨k.val, by omega⟩])
    (hr : ∀ k (_hk : j < k.val), g k = [f ⟨k.val + 1, by have := k.isLt; omega⟩]) :
    (List.ofFn g).flatten =
      (List.ofFn f).take j ++ g ⟨j, by omega⟩ ++ (List.ofFn f).drop (j + 2) := by
  have he : List.ofFn g =
      ((List.ofFn f).take j).map (fun x => [x]) ++
        g ⟨j, by omega⟩ :: ((List.ofFn f).drop (j + 2)).map (fun x => [x]) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append, List.length_map,
        List.length_take, List.length_cons, List.length_drop]
      omega
    · intro i hi hi'
      have hiN : i < N - 1 := by simpa only [List.length_ofFn] using hi
      have hj : min j N = j := by omega
      simp only [List.getElem_ofFn]
      by_cases hij : i < j
      · simp only [List.getElem_append, List.length_map, List.length_take,
          List.length_ofFn, hj,
          hij, ↓reduceDIte, List.getElem_map, List.getElem_take, List.getElem_ofFn]
        exact hl ⟨i, hiN⟩ hij
      · simp only [List.getElem_append, List.length_map, List.length_take,
          List.length_ofFn, hj,
          hij, ↓reduceDIte]
        by_cases heq : i = j
        · subst i
          simp
        · have hji : j < i := by omega
          simp only [List.getElem_cons, show i - j ≠ 0 by omega, ↓reduceDIte,
            List.getElem_map, List.getElem_drop, List.getElem_ofFn]
          exact (hr ⟨i, hiN⟩ hji).trans
            (congrArg (fun k => [f k]) (Fin.ext (by dsimp; omega)))
  have hs : ∀ l : List α, (l.map (fun x => [x])).flatten = l := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.flatten_cons, ih]
      rfl
  simp only [he, List.flatten_append, List.flatten_cons, hs, List.append_assoc]

end Langlands.FiniteConcatenation

namespace Langlands.PadicField.TopologicalData.SegmentProductDatum

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  {n : ℕ} (d : SegmentProductDatum.{uV,uF} T n)
  (j : ℕ) (h : j + 1 < d.length)
  (e₂ : SegmentProductDatum.{uV,uF} T
    ((d.shape.adjacentMerge j h).size (d.shape.adjacentMergeIndex j h)))

/-- Replace the actual inner datum at the merged slot, keeping every outside fiber. -/
def adjacentReplacementDatum (k : Fin (d.shape.adjacentMerge j h).length) :
    SegmentProductDatum.{uV,uF} T ((d.shape.adjacentMerge j h).size k) :=
  if hk : k = d.shape.adjacentMergeIndex j h then hk.symm ▸ e₂
  else d.adjacentDatum j h k

@[simp]
theorem adjacentReplacementDatum_merged :
    d.adjacentReplacementDatum j h e₂ (d.shape.adjacentMergeIndex j h) = e₂ := by
  simp only [adjacentReplacementDatum, ↓reduceDIte]

theorem adjacentReplacementDatum_of_ne
    (k : Fin (d.shape.adjacentMerge j h).length)
    (hk : k ≠ d.shape.adjacentMergeIndex j h) :
    d.adjacentReplacementDatum j h e₂ k = d.adjacentDatum j h k := by
  simp only [adjacentReplacementDatum, hk, ↓reduceDIte]

/-- Flatten the supplied replacement and all unchanged outside actual fibers. -/
def replaceAdjacentSlot : SegmentProductDatum.{uV,uF} T n :=
  concatenate (d.shape.adjacentMerge j h) (d.adjacentReplacementDatum j h e₂)

private theorem adjacentDatum_blockList_of_ne
    (k : Fin (d.shape.adjacentMerge j h).length) (hk : k.val ≠ j) :
    (d.adjacentDatum j h k).blockList =
      [d.blockAt ⟨k.val + if j < k.val then 1 else 0, by
        have := k.isLt
        change k.val < d.length - 1 at this
        split_ifs <;> omega⟩] := by
  rw [adjacentDatum_blockList,
    List.ofFn_congr (d.shape.adjacentRefinement_length_of_ne j h k hk)]
  simp only [List.ofFn_succ, List.ofFn_zero]
  congr 2
  apply Fin.ext
  exact (d.shape.adjacentBlockEquiv_val j h
    ⟨k, Fin.cast (d.shape.adjacentRefinement_length_of_ne j h k hk).symm 0⟩).trans
      (by simp)

/-- The replacement keeps the complete original prefix and suffix, in order. -/
theorem replaceAdjacentSlot_blockList :
    (d.replaceAdjacentSlot j h e₂).blockList =
      d.blockList.take j ++ e₂.blockList ++ d.blockList.drop (j + 2) := by
  change (concatenate _ _).blockList = _
  rw [concatenate_blockList]
  refine (FiniteConcatenation.flatten_ofFn_adjacent j h d.blockAt
    (fun k => (d.adjacentReplacementDatum j h e₂ k).blockList) ?_ ?_).trans ?_
  · intro k hk
    rw [adjacentReplacementDatum_of_ne _ _ _ _ k (by
      intro heq
      have := congrArg Fin.val heq
      change k.val = j at this
      omega), adjacentDatum_blockList_of_ne _ _ _ k (by omega)]
    simp only [show ¬ j < k.val by omega, ↓reduceIte, Nat.add_zero]
  · intro k hk
    rw [adjacentReplacementDatum_of_ne _ _ _ _ k (by
      intro heq
      have := congrArg Fin.val heq
      change k.val = j at this
      omega), adjacentDatum_blockList_of_ne _ _ _ k (by omega)]
    simp only [hk, ↓reduceIte]
  · exact congrArg (fun xs => d.blockList.take j ++ xs ++
      d.blockList.drop (j + 2))
      (congrArg blockList (d.adjacentReplacementDatum_merged j h e₂))

/-- The segment list is the exact indexed adjacent replacement. -/
theorem replaceAdjacentSlot_segments :
    List.ofFn (d.replaceAdjacentSlot j h e₂).segments =
      (List.ofFn d.segments).take j ++ List.ofFn e₂.segments ++
        (List.ofFn d.segments).drop (j + 2) := by
  rw [← blockList_segments, replaceAdjacentSlot_blockList]
  simp only [List.map_append, List.map_take, List.map_drop, blockList_segments]

/-- Strong segment socles are inherited from the original and supplied inner data. -/
theorem replaceAdjacentSlot_hasSegmentSocles
    (hd : d.HasSegmentSocles) (he₂ : e₂.HasSegmentSocles) :
    (d.replaceAdjacentSlot j h e₂).HasSegmentSocles := by
  apply concatenate_hasSegmentSocles
  intro k
  by_cases hk : k = d.shape.adjacentMergeIndex j h
  · subst k
    simpa only [adjacentReplacementDatum_merged] using he₂
  · rw [adjacentReplacementDatum_of_ne _ _ _ _ k hk]
    exact d.adjacentDatum_hasSegmentSocles j h hd k

/-- Closed regrouping from the common outer product to the replacement datum. -/
def replaceAdjacentSlotInducedEquiv :
    letI := T.topology
    (T.normalizedProductInduced (d.shape.adjacentMerge j h)
      (fun k => (d.adjacentReplacementDatum j h e₂ k).induced.representation)).Equiv
      (d.replaceAdjacentSlot j h e₂).induced.representation :=
  concatenateInducedEquiv _ _

end Langlands.PadicField.TopologicalData.SegmentProductDatum
