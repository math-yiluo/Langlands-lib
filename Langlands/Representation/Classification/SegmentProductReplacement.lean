import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.SegmentUnionIntersection
import Mathlib.Data.List.FinRange

/-! Actual block lists and fixed-rank segment-product replacement. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A segment together with a supplied actual representation of its degree. -/
abbrev SegmentBlock (T : F.TopologicalData) :=
  Σ Δ : Segment.{uV, uF} T, letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)

namespace SegmentBlock

/-- The actual block satisfies the strong segment-socle relation. -/
def IsSocle (b : SegmentBlock.{uF, uV} T) : Prop := T.IsSegmentSocle b.1 b.2

end SegmentBlock

namespace SegmentProductDatum

variable {n : ℕ}

/-- Package every original segment occurrence together with its actual block. -/
def blockList (d : SegmentProductDatum.{uV, uF} T n) : List (SegmentBlock.{uF, uV} T) :=
  List.ofFn fun i => ⟨d.segments i, d.blocks i⟩

@[simp]
theorem blockList_segments (d : SegmentProductDatum.{uV, uF} T n) :
    d.blockList.map Sigma.fst = List.ofFn d.segments := by
  simp [blockList, List.map_ofFn, Function.comp_def]

theorem blockList_degree_sum (d : SegmentProductDatum.{uV, uF} T n) :
    (d.blockList.map fun b => b.1.degree).sum = n := by
  simpa only [blockList, List.map_ofFn, Function.comp_def, List.sum_ofFn] using d.degree_sum

theorem blockList_isSocle_iff (d : SegmentProductDatum.{uV, uF} T n) :
    (∀ b ∈ d.blockList, b.IsSocle) ↔ d.HasSegmentSocles := by
  simp only [blockList, List.forall_mem_ofFn_iff, SegmentBlock.IsSocle, HasSegmentSocles]

/-- Turn an occurrence list of supplied blocks into actual data at the certified rank. -/
def ofBlockList (l : List (SegmentBlock.{uF, uV} T))
    (h : (l.map fun b => b.1.degree).sum = n) : SegmentProductDatum.{uV, uF} T n where
  length := l.length
  segments i := (l.get i).1
  degree_sum := by
    calc
      ∑ i : Fin l.length, (l.get i).1.degree =
          (List.ofFn fun i : Fin l.length => (l.get i).1.degree).sum := by
        rw [List.sum_ofFn]
      _ = (l.map fun b => b.1.degree).sum := by
        congr 1
        exact List.ofFn_getElem_eq_map l (fun b => b.1.degree)
      _ = n := h
  blocks i := (l.get i).2

@[simp]
theorem blockList_ofBlockList (l : List (SegmentBlock.{uF, uV} T))
    (h : (l.map fun b => b.1.degree).sum = n) :
    (ofBlockList l h).blockList = l := by
  change List.ofFn (fun i : Fin l.length => ⟨(l.get i).1, (l.get i).2⟩) = l
  simpa only [Sigma.eta] using List.ofFn_get l

@[simp]
theorem ofBlockList_segments (l : List (SegmentBlock.{uF, uV} T))
    (h : (l.map fun b => b.1.degree).sum = n) :
    List.ofFn (ofBlockList l h).segments = l.map Sigma.fst := by
  rw [← blockList_segments, blockList_ofBlockList]

theorem ofBlockList_hasSegmentSocles_iff (l : List (SegmentBlock.{uF, uV} T))
    (h : (l.map fun b => b.1.degree).sum = n) :
    (ofBlockList l h).HasSegmentSocles ↔ ∀ b ∈ l, b.IsSocle := by
  rw [← blockList_isSocle_iff, blockList_ofBlockList]

/-- Degree conservation for replacement of a displayed adjacent pair of
actual blocks. The complete original prefix and suffix are retained. -/
theorem replacementBlockList_degree_sum
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (d : SegmentProductDatum.{uV, uF} T n)
    {s t : List (SegmentBlock.{uF, uV} T)} {a b u : SegmentBlock.{uF, uV} T}
    {I : Option (SegmentBlock.{uF, uV} T)}
    (hd : d.blockList = s ++ a :: b :: t)
    (hs : Segment.IsUnionIntersectionReplacement a.1 b.1 u.1 (I.map Sigma.fst))
    (hp : a.1.Precedes b.1) :
    ((s ++ [u] ++ I.toList ++ t).map fun b => b.1.degree).sum = n := by
  have hold := d.blockList_degree_sum
  rw [hd] at hold
  have hpair : u.1.degree + (I.toList.map fun c => c.1.degree).sum =
      a.1.degree + b.1.degree := by
    simpa only [Option.toList_map, List.map_map, Function.comp_def] using
      hs.degree_sum hfree hp
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero] at hold ⊢
  omega

/-- Replace a preceding pair by supplied actual union and optional
intersection blocks, without changing rank or any outside actual block. -/
def replacePair
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (d : SegmentProductDatum.{uV, uF} T n)
    {s t : List (SegmentBlock.{uF, uV} T)} {a b : SegmentBlock.{uF, uV} T}
    (hd : d.blockList = s ++ a :: b :: t)
    (u : SegmentBlock.{uF, uV} T) (I : Option (SegmentBlock.{uF, uV} T))
    (hs : Segment.IsUnionIntersectionReplacement a.1 b.1 u.1 (I.map Sigma.fst))
    (hp : a.1.Precedes b.1) : SegmentProductDatum.{uV, uF} T n :=
  ofBlockList (s ++ [u] ++ I.toList ++ t)
    (replacementBlockList_degree_sum hfree d hd hs hp)

@[simp]
theorem blockList_replacePair
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (d : SegmentProductDatum.{uV, uF} T n)
    {s t : List (SegmentBlock.{uF, uV} T)} {a b : SegmentBlock.{uF, uV} T}
    (hd : d.blockList = s ++ a :: b :: t)
    (u : SegmentBlock.{uF, uV} T) (I : Option (SegmentBlock.{uF, uV} T))
    (hs : Segment.IsUnionIntersectionReplacement a.1 b.1 u.1 (I.map Sigma.fst))
    (hp : a.1.Precedes b.1) :
    (d.replacePair hfree hd u I hs hp).blockList = s ++ [u] ++ I.toList ++ t :=
  blockList_ofBlockList _ _

theorem replacePair_hasSegmentSocles
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (d : SegmentProductDatum.{uV, uF} T n)
    {s t : List (SegmentBlock.{uF, uV} T)} {a b : SegmentBlock.{uF, uV} T}
    (hd : d.blockList = s ++ a :: b :: t)
    (u : SegmentBlock.{uF, uV} T) (I : Option (SegmentBlock.{uF, uV} T))
    (hs : Segment.IsUnionIntersectionReplacement a.1 b.1 u.1 (I.map Sigma.fst))
    (hp : a.1.Precedes b.1) (hdSocle : d.HasSegmentSocles)
    (hu : u.IsSocle) (hI : ∀ v ∈ I.toList, v.IsSocle) :
    (d.replacePair hfree hd u I hs hp).HasSegmentSocles := by
  rw [← blockList_isSocle_iff, blockList_replacePair]
  have hold := (d.blockList_isSocle_iff).mpr hdSocle
  intro v hv
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with ((hv | hv) | hv) | hv
  · apply hold v
    rw [hd]
    simp [hv]
  · subst v
    exact hu
  · exact hI v hv
  · apply hold v
    rw [hd]
    simp [hv]

end SegmentProductDatum

end Langlands.PadicField.TopologicalData
