import Langlands.Representation.Classification.SegmentProductReplacement
import Mathlib.Data.List.TakeDrop

/-! Indexed replacement of adjacent actual segment blocks. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace SegmentProductDatum

variable {n : ℕ}

/-- A particular segment occurrence together with its supplied actual block. -/
def blockAt (d : SegmentProductDatum.{uV, uF} T n) (i : Fin d.length) :
    SegmentBlock.{uF, uV} T := ⟨d.segments i, d.blocks i⟩

@[simp]
theorem blockList_getElem (d : SegmentProductDatum.{uV, uF} T n)
    (j : ℕ) (h : j < d.blockList.length) :
    d.blockList[j] = d.blockAt ⟨j, by simpa only [blockList, List.length_ofFn] using h⟩ := by
  simp only [blockList, List.getElem_ofFn, blockAt]

/-- Recover the displayed adjacent pair without changing any actual block. -/
theorem blockList_adjacent_decomposition
    (d : SegmentProductDatum.{uV, uF} T n) (j : ℕ) (h : j + 1 < d.length) :
    d.blockList = d.blockList.take j ++
      d.blockAt ⟨j, by omega⟩ :: d.blockAt ⟨j + 1, h⟩ ::
        d.blockList.drop (j + 2) := by
  have h0 : j < d.blockList.length := by
    simp only [blockList, List.length_ofFn]
    omega
  have h1 : j + 1 < d.blockList.length := by
    simpa only [blockList, List.length_ofFn] using h
  calc
    d.blockList = d.blockList.take j ++ d.blockList.drop j :=
      (List.take_append_drop j d.blockList).symm
    _ = _ := by
      rw [List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1]
      simp only [blockList_getElem, Nat.add_assoc]

/-- Replace a preceding adjacent pair with supplied actual union and optional
intersection blocks at the same total rank. -/
def replaceAdjacentPair
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (d : SegmentProductDatum.{uV, uF} T n) (j : ℕ) (h : j + 1 < d.length)
    (u : SegmentBlock.{uF, uV} T) (I : Option (SegmentBlock.{uF, uV} T))
    (hs : Segment.IsUnionIntersectionReplacement
      (d.segments ⟨j, by omega⟩) (d.segments ⟨j + 1, h⟩) u.1 (I.map Sigma.fst))
    (hp : (d.segments ⟨j, by omega⟩).Precedes (d.segments ⟨j + 1, h⟩)) :
    SegmentProductDatum.{uV, uF} T n :=
  d.replacePair hfree (d.blockList_adjacent_decomposition j h) u I hs hp

@[simp]
theorem blockList_replaceAdjacentPair
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (d : SegmentProductDatum.{uV, uF} T n) (j : ℕ) (h : j + 1 < d.length)
    (u : SegmentBlock.{uF, uV} T) (I : Option (SegmentBlock.{uF, uV} T))
    (hs : Segment.IsUnionIntersectionReplacement
      (d.segments ⟨j, by omega⟩) (d.segments ⟨j + 1, h⟩) u.1 (I.map Sigma.fst))
    (hp : (d.segments ⟨j, by omega⟩).Precedes (d.segments ⟨j + 1, h⟩)) :
    (d.replaceAdjacentPair hfree j h u I hs hp).blockList =
      d.blockList.take j ++ [u] ++ I.toList ++ d.blockList.drop (j + 2) :=
  blockList_replacePair _ _ _ _ _ _ _

/-- The segment list is exactly the indexed union/intersection replacement. -/
theorem ofFn_replaceAdjacentPair
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (d : SegmentProductDatum.{uV, uF} T n) (j : ℕ) (h : j + 1 < d.length)
    (u : SegmentBlock.{uF, uV} T) (I : Option (SegmentBlock.{uF, uV} T))
    (hs : Segment.IsUnionIntersectionReplacement
      (d.segments ⟨j, by omega⟩) (d.segments ⟨j + 1, h⟩) u.1 (I.map Sigma.fst))
    (hp : (d.segments ⟨j, by omega⟩).Precedes (d.segments ⟨j + 1, h⟩)) :
    List.ofFn (d.replaceAdjacentPair hfree j h u I hs hp).segments =
      (List.ofFn d.segments).take j ++ [u.1] ++ (I.map Sigma.fst).toList ++
        (List.ofFn d.segments).drop (j + 2) := by
  rw [← blockList_segments, blockList_replaceAdjacentPair]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_take,
    List.map_drop, blockList_segments, Option.toList_map]

theorem replaceAdjacentPair_hasSegmentSocles
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (d : SegmentProductDatum.{uV, uF} T n) (j : ℕ) (h : j + 1 < d.length)
    (u : SegmentBlock.{uF, uV} T) (I : Option (SegmentBlock.{uF, uV} T))
    (hs : Segment.IsUnionIntersectionReplacement
      (d.segments ⟨j, by omega⟩) (d.segments ⟨j + 1, h⟩) u.1 (I.map Sigma.fst))
    (hp : (d.segments ⟨j, by omega⟩).Precedes (d.segments ⟨j + 1, h⟩))
    (hdSocle : d.HasSegmentSocles) (hu : u.IsSocle)
    (hI : ∀ v ∈ I.toList, v.IsSocle) :
    (d.replaceAdjacentPair hfree j h u I hs hp).HasSegmentSocles :=
  d.replacePair_hasSegmentSocles hfree (d.blockList_adjacent_decomposition j h)
    u I hs hp hdSocle hu hI

end SegmentProductDatum

end Langlands.PadicField.TopologicalData
