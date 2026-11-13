import Langlands.Representation.Classification.A6iiMerge
import Langlands.Representation.Classification.A6iiSorting
import Langlands.Representation.Classification.SegmentProductConcatenation

/-!
# The merged segment datum

A segment-product datum is reordered along the members of a stable merge
grouping. The reordered datum has the same multisegment, its shape is the
flattened group shape, and decreasing chosen exponents make it precedence-ordered.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

section Merged

variable {n : ℕ} (c : T.SegmentProductDatum.{uV, uF} n) {ex : Fin c.length → ℝ}
  (m : MergeGrouping n (fun ℓ => (c.segments ℓ).degree) ex)

/-- The degrees of the segments are positive. -/
theorem degree_pos_family (ℓ : Fin c.length) : 0 < (fun ℓ => (c.segments ℓ).degree) ℓ :=
  (c.segments ℓ).degree_pos

/-- The member refinement of the groups. -/
abbrev mergedRefinement : Geometric.BlockRefinement m.shape :=
  m.refinement (degree_pos_family c)

/-- The label of a flattened member. -/
abbrev mergedLabel (k : Fin (m.shape.flatten (mergedRefinement c m)).length) : Fin c.length :=
  m.label ((m.shape.flattenBlockEquiv (mergedRefinement c m)).symm k)

/-- The datum listing the segments and blocks group by group. -/
def merged : T.SegmentProductDatum.{uV, uF} n where
  length := (m.shape.flatten (mergedRefinement c m)).length
  segments k := c.segments (mergedLabel c m k)
  degree_sum := (m.shape.flatten (mergedRefinement c m)).sum_eq
  blocks k := c.blocks (mergedLabel c m k)

theorem merged_shape : (merged c m).shape = m.shape.flatten (mergedRefinement c m) := rfl

/-- The flattened members are numbered by an equivalence with the labels. -/
def mergedEquiv : Fin (merged c m).length ≃ Fin c.length :=
  (m.shape.flattenBlockEquiv (mergedRefinement c m)).symm.trans m.label

theorem mergedEquiv_apply (k : Fin (merged c m).length) :
    mergedEquiv c m k = mergedLabel c m k := rfl

theorem merged_multisegment : (merged c m).multisegment = c.multisegment := by
  change ((List.ofFn (fun k => c.segments (mergedEquiv c m k)) :
      Multiset (Segment.{uV, uF} T))) = (List.ofFn c.segments : Multiset _)
  rw [← Fin.univ_val_map, ← Fin.univ_val_map,
    show (fun k => c.segments (mergedEquiv c m k)) = c.segments ∘ mergedEquiv c m from rfl,
    ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem merged_hasSegmentHeads (hh : c.HasSegmentHeads) : (merged c m).HasSegmentHeads :=
  fun k => hh (mergedLabel c m k)

end Merged

section MergedOrder

variable {n : ℕ} (c : T.SegmentProductDatum.{max uF uV, uF} n) {ex : Fin c.length → ℝ}
  (m : MergeGrouping n (fun ℓ => (c.segments ℓ).degree) ex)

variable (F T) in
/-- Exponents decreasing along the merge make the merged datum precedence-ordered. -/
theorem merged_isPrecedenceOrdered (hh : c.HasSegmentHeads)
    (u : letI := T.topology
      ∀ ℓ, UnitaryExponentData (T.determinantNorm (c.segments ℓ).degree)
        (c.blocks ℓ).representation)
    (hex : ∀ ℓ, ex ℓ = (u ℓ).exponent) :
    (merged c m).IsPrecedenceOrdered := by
  apply isPrecedenceOrdered_of_antitone F T (merged c m) (merged_hasSegmentHeads c m hh)
    (fun k => u (mergedLabel c m k))
  intro k k' hkk'
  have h := m.antitone_exponent (degree_pos_family c) hkk'
  simp only [hex] at h
  exact h

end MergedOrder

section Concatenation

variable {n : ℕ} (B : BlockShape n) (a : ∀ i, T.SegmentProductDatum.{uV, uF} (B.size i))

/-- The multisegment of a concatenation is the sum of the multisegments. -/
theorem concatenate_multisegment :
    (SegmentProductDatum.concatenate B a).multisegment = ∑ i, (a i).multisegment := by
  change ((List.ofFn (SegmentProductDatum.concatenate B a).segments :
      Multiset (Segment.{uV, uF} T))) = _
  rw [SegmentProductDatum.concatenate_segments, ← Multiset.coe_join, List.map_ofFn]
  change Multiset.sum ((List.ofFn fun i => (a i).multisegment :
      List (Multiset (Segment.{uV, uF} T))) : Multiset (Multiset (Segment.{uV, uF} T))) = _
  rw [Multiset.sum_coe, List.sum_ofFn]

/-- Segment heads survive concatenation. -/
theorem concatenate_hasSegmentHeads (ha : ∀ i, (a i).HasSegmentHeads) :
    (SegmentProductDatum.concatenate B a).HasSegmentHeads :=
  fun l => ha (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2

end Concatenation

end Langlands.Classification.A6ii
