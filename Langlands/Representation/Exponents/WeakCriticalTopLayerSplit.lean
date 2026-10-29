import Langlands.Representation.Exponents.WeakCritical
import Langlands.Representation.Classification.MaximalConeExponents
import Langlands.Representation.Classification.ParabolicConeSubgroupProof
import Langlands.Group.GL.ConjugatePairRefinementRankProof
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Classification.MaximalConeLifting

/-!
# Splitting one block of a standard shape along a flattened refinement

For a standard block shape `B` and a block refinement `D`, every flattened block
lies in one outer block. Cutting one outer block `j` after its inner block `i`
gives a standard shape `C'` with one more block. The shape `C'` is a consecutive
coarsening of the flattened shape and a consecutive refinement of `B`, and its
standard pair strictly refines the standard pair of `B`.
-/

noncomputable section

namespace Langlands

open Geometric
open scoped BigOperators

namespace GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n) (D : BlockRefinement B)

theorem refinement_length_pos (j : Fin B.length) : 0 < (D j).length := by
  rcases Nat.eq_zero_or_pos (D j).length with h | h
  · exfalso
    have hs := (D j).sum_eq
    have h0 : ∑ i : Fin (D j).length, (D j).size i = 0 :=
      Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega)
    have := B.positive j
    omega
  · exact h

section Split

variable (j : Fin B.length) (i : Fin (D j).length)

/-- The flattened label of the last inner block before the cut. -/
def splitCut : Fin (B.flatten D).length := B.flattenBlockEquiv D ⟨j, i⟩

theorem splitCut_lt_iff (x : (i : Fin B.length) × Fin (D i).length) :
    B.splitCut D j i < B.flattenBlockEquiv D x ↔ j < x.1 ∨ (j = x.1 ∧ i.val < x.2.val) :=
  B.flattenBlockEquiv_lt_iff D ⟨j, i⟩ x

theorem flattenOuter_le_of_not_lt {k : Fin (B.flatten D).length}
    (hk : ¬ B.splitCut D j i < k) : B.flattenOuter D k ≤ j := by
  have h := B.flattenOuter_mono D (not_lt.mp hk)
  simpa [splitCut] using h

theorem le_flattenOuter_of_lt {k : Fin (B.flatten D).length}
    (hk : B.splitCut D j i < k) : j ≤ B.flattenOuter D k := by
  have h := B.flattenOuter_mono D hk.le
  simpa [splitCut] using h

/-- The coarse label of a flattened block after cutting block `j` after `i`. -/
def splitIndex (k : Fin (B.flatten D).length) : Fin (B.length + 1) :=
  ⟨(B.flattenOuter D k).val + (if B.splitCut D j i < k then 1 else 0), by
    have := (B.flattenOuter D k).isLt
    split_ifs <;> omega⟩

theorem splitIndex_val (k : Fin (B.flatten D).length) :
    (B.splitIndex D j i k).val =
      (B.flattenOuter D k).val + (if B.splitCut D j i < k then 1 else 0) := rfl

theorem splitIndex_val_of_lt {k : Fin (B.flatten D).length} (h : B.splitCut D j i < k) :
    (B.splitIndex D j i k).val = (B.flattenOuter D k).val + 1 := by
  simp [splitIndex_val, h]

theorem splitIndex_val_of_not_lt {k : Fin (B.flatten D).length}
    (h : ¬ B.splitCut D j i < k) :
    (B.splitIndex D j i k).val = (B.flattenOuter D k).val := by
  simp [splitIndex_val, h]

theorem splitIndex_monotone : Monotone (B.splitIndex D j i) := by
  intro k k' hkk'
  have ho := B.flattenOuter_mono D hkk'
  change (B.splitIndex D j i k).val ≤ (B.splitIndex D j i k').val
  rw [splitIndex_val, splitIndex_val]
  have ho' : (B.flattenOuter D k).val ≤ (B.flattenOuter D k').val := ho
  by_cases h : B.splitCut D j i < k
  · have h' : B.splitCut D j i < k' := lt_of_lt_of_le h hkk'
    simp only [h, h', ite_true]
    omega
  · simp only [h, ite_false]
    split_ifs <;> omega

theorem splitIndex_surjective (hi : i.val + 1 < (D j).length) :
    Function.Surjective (B.splitIndex D j i) := by
  intro l
  rcases lt_trichotomy l.val j.val with hl | hl | hl
  · let j' : Fin B.length := ⟨l.val, by omega⟩
    let x : (i : Fin B.length) × Fin (D i).length :=
      ⟨j', ⟨0, B.refinement_length_pos D j'⟩⟩
    refine ⟨B.flattenBlockEquiv D x, Fin.ext ?_⟩
    have hn : ¬ B.splitCut D j i < B.flattenBlockEquiv D x := by
      rw [splitCut_lt_iff]
      change ¬ (j < j' ∨ (j = j' ∧ _))
      have : ¬ j < j' := by
        change ¬ j.val < l.val
        omega
      have : j ≠ j' := by
        intro h
        have := congrArg Fin.val h
        change j.val = l.val at this
        omega
      tauto
    rw [splitIndex_val_of_not_lt B D j i hn, flattenOuter_flattenBlockEquiv]
  · refine ⟨B.splitCut D j i, Fin.ext ?_⟩
    rw [splitIndex_val_of_not_lt B D j i (lt_irrefl _)]
    simp [splitCut, hl]
  · rcases Nat.lt_or_ge (j.val + 1) l.val with hl' | hl'
    · let j' : Fin B.length := ⟨l.val - 1, by omega⟩
      let x : (i : Fin B.length) × Fin (D i).length :=
        ⟨j', ⟨0, B.refinement_length_pos D j'⟩⟩
      refine ⟨B.flattenBlockEquiv D x, Fin.ext ?_⟩
      have hy : B.splitCut D j i < B.flattenBlockEquiv D x := by
        rw [splitCut_lt_iff]
        left
        change j.val < l.val - 1
        omega
      rw [splitIndex_val_of_lt B D j i hy, flattenOuter_flattenBlockEquiv]
      change l.val - 1 + 1 = l.val
      omega
    · let x : (i : Fin B.length) × Fin (D i).length := ⟨j, ⟨i.val + 1, hi⟩⟩
      refine ⟨B.flattenBlockEquiv D x, Fin.ext ?_⟩
      have hy : B.splitCut D j i < B.flattenBlockEquiv D x := by
        rw [splitCut_lt_iff]
        right
        exact ⟨rfl, Nat.lt_succ_self _⟩
      rw [splitIndex_val_of_lt B D j i hy, flattenOuter_flattenBlockEquiv]
      change j.val + 1 = l.val
      omega

/-- The shape obtained by cutting block `j` after its inner block `i`. -/
def splitShape (hi : i.val + 1 < (D j).length) : BlockShape n where
  length := B.length + 1
  size l := ∑ k ∈ Finset.univ.filter (fun k => B.splitIndex D j i k = l), (B.flatten D).size k
  positive l := by
    obtain ⟨k, hk⟩ := B.splitIndex_surjective D j i hi l
    exact Finset.sum_pos (fun k _ => (B.flatten D).positive k) ⟨k, by simp [hk]⟩
  sum_eq := by
    rw [Finset.sum_fiberwise Finset.univ (B.splitIndex D j i) (B.flatten D).size,
      (B.flatten D).sum_eq]

/-- The merge map from the split shape back to `B`. -/
def splitMerge (l : Fin (B.length + 1)) : Fin B.length :=
  if h : l.val ≤ j.val then ⟨l.val, by omega⟩ else ⟨l.val - 1, by omega⟩

theorem splitMerge_val_of_le {l : Fin (B.length + 1)} (h : l.val ≤ j.val) :
    (B.splitMerge j l).val = l.val := by
  simp [splitMerge, h]

theorem splitMerge_val_of_not_le {l : Fin (B.length + 1)} (h : ¬ l.val ≤ j.val) :
    (B.splitMerge j l).val = l.val - 1 := by
  simp [splitMerge, h]

theorem splitMerge_monotone : Monotone (B.splitMerge j) := by
  intro l l' hll'
  have h : l.val ≤ l'.val := hll'
  change (B.splitMerge j l).val ≤ (B.splitMerge j l').val
  unfold splitMerge
  split_ifs <;> simp only <;> omega

theorem splitMerge_surjective : Function.Surjective (B.splitMerge j) := by
  intro j'
  by_cases h : j'.val ≤ j.val
  · refine ⟨⟨j'.val, by omega⟩, Fin.ext ?_⟩
    simp [splitMerge, h]
  · refine ⟨⟨j'.val + 1, by omega⟩, Fin.ext ?_⟩
    have h' : ¬ j'.val + 1 ≤ j.val := by omega
    simp [splitMerge, h']

theorem splitMerge_splitIndex (k : Fin (B.flatten D).length) :
    B.splitMerge j (B.splitIndex D j i k) = B.flattenOuter D k := by
  apply Fin.ext
  by_cases h : B.splitCut D j i < k
  · have hj := B.le_flattenOuter_of_lt D j i h
    have hj' : j.val ≤ (B.flattenOuter D k).val := hj
    have hn : ¬ (B.splitIndex D j i k).val ≤ j.val := by
      rw [B.splitIndex_val_of_lt D j i h]
      omega
    rw [B.splitMerge_val_of_not_le j hn, B.splitIndex_val_of_lt D j i h]
    simp
  · have hj := B.flattenOuter_le_of_not_lt D j i h
    have hj' : (B.flattenOuter D k).val ≤ j.val := hj
    have hp : (B.splitIndex D j i k).val ≤ j.val := by
      rw [B.splitIndex_val_of_not_lt D j i h]
      omega
    rw [B.splitMerge_val_of_le j hp, B.splitIndex_val_of_not_lt D j i h]

theorem splitMerge_comp_splitIndex :
    B.splitMerge j ∘ B.splitIndex D j i = B.flattenOuter D :=
  funext (B.splitMerge_splitIndex D j i)

variable (hi : i.val + 1 < (D j).length)

@[simp] theorem splitShape_length : (B.splitShape D j i hi).length = B.length + 1 := rfl

theorem splitShape_size (l : Fin (B.length + 1)) :
    (B.splitShape D j i hi).size l =
      ∑ k ∈ Finset.univ.filter (fun k => B.splitIndex D j i k = l), (B.flatten D).size k :=
  rfl

theorem size_eq_sum_splitMerge (j' : Fin B.length) :
    B.size j' = ∑ l ∈ Finset.univ.filter
      (fun l : Fin (B.length + 1) => B.splitMerge j l = j'),
        (B.splitShape D j i hi).size l := by
  classical
  rw [B.size_eq_sum_flattenOuter D j']
  simp only [splitShape_size]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun k => B.flattenOuter D k = j'))
    (t := Finset.univ.filter (fun l : Fin (B.length + 1) => B.splitMerge j l = j'))
    (g := B.splitIndex D j i)
    (by intro k hk; simpa [B.splitMerge_splitIndex D j i] using hk)]
  refine Finset.sum_congr rfl fun l hl => Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    rw [← B.splitMerge_splitIndex D j i k, h, hl]

theorem splitMerge_comp_comp_splitIndex {α : Type*} (a : Fin B.length → α) :
    (a ∘ B.splitMerge j) ∘ B.splitIndex D j i = a ∘ B.flattenOuter D :=
  funext fun k => congrArg a (B.splitMerge_splitIndex D j i k)

/-- Block scalars of `B` are block scalars of the split shape. -/
theorem splitShape_blockScalar (K : Type*) [CommRing K] (a : Fin B.length → Kˣ) :
    (B.splitShape D j i hi).blockScalar K (a ∘ B.splitMerge j) = B.blockScalar K a :=
  leviEmbedding_blockScalarLevi_coarsen K (B.splitMerge_monotone j)
    (B.size_eq_sum_splitMerge D j i hi) a

/-- The standard pair of the split shape refines the standard pair of `B`. -/
theorem standard_splitShape_refines (K : Type*) [CommRing K] :
    (Exponents.ConjugateBlockPair.standard (R := K) (B.splitShape D j i hi)).Refines
      (Exponents.ConjugateBlockPair.standard B) := by
  constructor
  · rw [Exponents.ConjugateBlockPair.standard_parabolic,
      Exponents.ConjugateBlockPair.standard_parabolic]
    exact (glBlockCoarseningSubgroups n (B.splitShape D j i hi) B (B.splitMerge j)
      (B.splitMerge_monotone j) (B.splitMerge_surjective j)
      (B.size_eq_sum_splitMerge D j i hi) K).1
  · rintro _ ⟨a, rfl⟩
    refine ⟨a ∘ B.splitMerge j, ?_⟩
    simp only [Exponents.ConjugateBlockPair.standard_scalarMap]
    exact B.splitShape_blockScalar D j i hi K a

/-- The refinement is strict, since the split shape has one more block. -/
theorem standard_splitShape_strictlyRefines (K : Type*) [Field K]
    (ht : ∃ t : K, t ≠ 0 ∧ t ≠ 1) :
    (Exponents.ConjugateBlockPair.standard (R := K) (B.splitShape D j i hi)).StrictlyRefines
      (Exponents.ConjugateBlockPair.standard B) := by
  refine ⟨B.standard_splitShape_refines D j i hi K, fun h => ?_⟩
  have hl := ConjugatePairRefinementRankProof.length_le_of_splitComponent_le ht h.2
  change B.length + 1 ≤ B.length at hl
  omega

/-- The coarse labels, typed by the split shape. -/
def splitLabel : Fin (B.flatten D).length → Fin (B.splitShape D j i hi).length :=
  B.splitIndex D j i

/-- The merge map, typed by the split shape. -/
def splitMergeLabel : Fin (B.splitShape D j i hi).length → Fin B.length :=
  B.splitMerge j

theorem splitLabel_monotone : Monotone (B.splitLabel D j i hi) :=
  B.splitIndex_monotone D j i

theorem splitShape_size_eq_sum_splitLabel (l : Fin (B.splitShape D j i hi).length) :
    (B.splitShape D j i hi).size l =
      ∑ k ∈ Finset.univ.filter (fun k => B.splitLabel D j i hi k = l), (B.flatten D).size k :=
  rfl

theorem splitMergeLabel_monotone : Monotone (B.splitMergeLabel D j i hi) :=
  B.splitMerge_monotone j

theorem size_eq_sum_splitMergeLabel (j' : Fin B.length) :
    B.size j' = ∑ l ∈ Finset.univ.filter (fun l => B.splitMergeLabel D j i hi l = j'),
      (B.splitShape D j i hi).size l :=
  B.size_eq_sum_splitMerge D j i hi j'

theorem splitMergeLabel_comp_splitLabel {α : Type*} (a : Fin B.length → α) :
    (a ∘ B.splitMergeLabel D j i hi) ∘ B.splitLabel D j i hi = a ∘ B.flattenOuter D :=
  B.splitMerge_comp_comp_splitIndex D j i a

end Split

end GeneralLinear.BlockShape

end Langlands
