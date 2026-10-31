import Langlands.Representation.Classification.UniformRefinementCombinatorics
import Langlands.Representation.Classification.UniformTargetBlockLabels
import Mathlib.Order.Interval.Finset.Fin

/-! Coordinates and ordered block positions of uniform source refinements. -/

noncomputable section

namespace Langlands.Classification.ShuffleRefinement

open GeneralLinear Geometric

variable {K : Type*} [Field K]
variable {m r : ℕ} (hr : 0 < r)
variable (B : BlockShape (m * r)) (w : Equiv.Perm (Fin (m * r)))
variable (S : BlockRefinement B)
variable (hS : sourceLevi K B (BlockShape.uniform m r hr) w = refinedLevi K B S)
variable (hw : IsMinimalRepresentative B (BlockShape.uniform m r hr) w)

/-- The target block containing the image of a source refinement piece. -/
def refinementTargetIndex (j : Fin B.length) (i : Fin (S j).length) : Fin m :=
  blockIndex (BlockShape.uniform m r hr)
    (w (B.index j ((S j).index i ⟨0, (S j).positive i⟩)))

include hS in
theorem refinementTargetIndex_injective (j : Fin B.length) :
    Function.Injective (refinementTargetIndex hr B w S j) := by
  intro i k hik
  have h := (SegmentEdge.sameBlock_of_sourceLevi_eq B
    (BlockShape.uniform m r hr) w S hS j _ _).mpr hik
  simpa only [blockIndex_index] using h

include hS hw in
/-- On a surviving refinement piece the actual permutation preserves the
coordinate within its whole target block. -/
theorem source_piece_coordinates (j : Fin B.length) (i : Fin (S j).length)
    (hi : r ∣ (S j).size i) (a : Fin ((S j).size i)) :
    w (B.index j ((S j).index i a)) =
      (BlockShape.uniform m r hr).index (refinementTargetIndex hr B w S j i)
        (Fin.cast (source_size_eq_of_dvd hr B w S hS j i hi) a) := by
  let C := BlockShape.uniform m r hr
  let t := refinementTargetIndex hr B w S j i
  let he := source_size_eq_of_dvd hr B w S hS j i hi
  have hf : StrictMono (fun a : Fin ((S j).size i) =>
      w (B.index j ((S j).index i a))) :=
    (hw.1 j).comp (index_strictMono (S j) i)
  have hg : StrictMono (fun a : Fin ((S j).size i) =>
      C.index t (Fin.cast he a)) :=
    (index_strictMono C t).comp (Fin.cast_strictMono he)
  apply congrFun (hf.eq_of_range_eq hg ?_) a
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    have hb := (sourceBlockEmbedding B C w S hS j i b).property
    obtain ⟨z, hz⟩ := exists_index_of_blockIndex_eq C hb
    refine ⟨Fin.cast he.symm z, ?_⟩
    have hez : Fin.cast he (Fin.cast he.symm z) = z := Fin.ext rfl
    exact (congrArg (C.index t) hez).trans hz
  · rintro ⟨b, rfl⟩
    obtain ⟨z, hz⟩ := sourceBlockEmbedding_surjective hr B w S hS j i hi
      ⟨C.index t (Fin.cast he b), blockIndex_index C t _⟩
    exact ⟨z, congrArg Subtype.val hz⟩

include hS hw in
theorem inverse_source_piece_coordinates (j : Fin B.length) (i : Fin (S j).length)
    (hi : r ∣ (S j).size i) (a : Fin ((S j).size i)) :
    w.symm ((BlockShape.uniform m r hr).index
      (refinementTargetIndex hr B w S j i)
        (Fin.cast (source_size_eq_of_dvd hr B w S hS j i hi) a)) =
      B.index j ((S j).index i a) := by
  rw [← source_piece_coordinates hr B w S hS hw j i hi a, Equiv.symm_apply_apply]

include hS hw in
theorem refinementTargetIndex_label (j : Fin B.length) (i : Fin (S j).length)
    (hi : r ∣ (S j).size i) :
    targetBlockLabel B (BlockShape.uniform m r hr) w
      (refinementTargetIndex hr B w S j i) = j := by
  have h := inverse_source_piece_coordinates hr B w S hS hw j i hi
    ⟨0, (S j).positive i⟩
  change w.symm ((BlockShape.uniform m r hr).index
    (refinementTargetIndex hr B w S j i) ⟨0, hr⟩) =
      B.index j ((S j).index i ⟨0, (S j).positive i⟩) at h
  dsimp only [targetBlockLabel]
  rw [h, blockIndex_index]

include hS hw in
theorem refinementTargetIndex_strictMono (j : Fin B.length) :
    StrictMono (refinementTargetIndex hr B w S j) := by
  apply (show Monotone (refinementTargetIndex hr B w S j) from ?_).strictMono_of_injective
    (refinementTargetIndex_injective hr B w S hS j)
  intro i k hik
  rcases lt_or_eq_of_le hik with hik | rfl
  · exact blockIndex_monotone (BlockShape.uniform m r hr)
      ((hw.1 j) ((S j).index_lt_index_of_block_lt hik _ _)).le
  · exact le_rfl

/-- The target blocks assigned to a given source block. -/
def sourceTargetBlocks (j : Fin B.length) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter
    (fun t => targetBlockLabel B (BlockShape.uniform m r hr) w t = j)

include hS hw in
theorem card_sourceTargetBlocks (hdiv : ∀ j i, r ∣ (S j).size i)
    (j : Fin B.length) :
    (sourceTargetBlocks hr B w j).card = (S j).length := by
  classical
  let whole : WholeTargetRepresentatives hr B :=
    ⟨⟨w, hw⟩, inverse_same_source_block hr B w S hS hdiv⟩
  have hc := targetBlockLabel_card hr B whole j
  have hf : Nat.card {t : Fin m //
      targetBlockLabel B (BlockShape.uniform m r hr) w t = j} =
      (sourceTargetBlocks hr B w j).card := by
    simp only [sourceTargetBlocks, Nat.card_eq_fintype_card, Fintype.subtype_card]
  rw [hf] at hc
  apply Nat.eq_of_mul_eq_mul_right hr
  calc
    (sourceTargetBlocks hr B w j).card * r = B.size j := hc
    _ = ∑ i, (S j).size i := (S j).sum_eq.symm
    _ = (S j).length * r := by
      simp [source_size_eq_of_dvd hr B w S hS j, hdiv]

include hS hw in
/-- Source refinement pieces enumerate their assigned target blocks increasingly. -/
theorem refinementTargetIndex_eq_orderEmbOfFin (hdiv : ∀ j i, r ∣ (S j).size i)
    (j : Fin B.length) :
    refinementTargetIndex hr B w S j =
      (sourceTargetBlocks hr B w j).orderEmbOfFin
        (card_sourceTargetBlocks hr B w S hS hw hdiv j) := by
  classical
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      refinementTargetIndex_label hr B w S hS hw j i (hdiv j i)⟩
  · exact refinementTargetIndex_strictMono hr B w S hS hw j

include hS hw in
/-- The piece number is the number of earlier target blocks with the same
source label. -/
theorem card_sourceTargetBlocks_before (hdiv : ∀ j i, r ∣ (S j).size i)
    (j : Fin B.length) (i : Fin (S j).length) :
    ((sourceTargetBlocks hr B w j).filter
      (· < refinementTargetIndex hr B w S j i)).card = i.val := by
  classical
  let s := sourceTargetBlocks hr B w j
  let hc := card_sourceTargetBlocks hr B w S hS hw hdiv j
  let e := s.orderEmbOfFin hc
  have he : refinementTargetIndex hr B w S j = e :=
    refinementTargetIndex_eq_orderEmbOfFin hr B w S hS hw hdiv j
  change (s.filter (· < refinementTargetIndex hr B w S j i)).card = i.val
  rw [he]
  have hset : s.filter (· < e i) = (Finset.Iio i).image e := by
    ext t
    constructor
    · intro ht
      have htr : t ∈ Set.range e := by
        rw [show Set.range e = (s : Set (Fin m)) from Finset.range_orderEmbOfFin s hc]
        exact (Finset.mem_filter.mp ht).1
      obtain ⟨k, rfl⟩ := htr
      exact Finset.mem_image.mpr ⟨k,
        Finset.mem_Iio.mpr (e.lt_iff_lt.mp (Finset.mem_filter.mp ht).2), rfl⟩
    · intro ht
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_filter.mpr
        ⟨s.orderEmbOfFin_mem hc k, e.strictMono (Finset.mem_Iio.mp hk)⟩
  rw [hset, Finset.card_image_of_injective _ e.injective, Fin.card_Iio]

end Langlands.Classification.ShuffleRefinement
