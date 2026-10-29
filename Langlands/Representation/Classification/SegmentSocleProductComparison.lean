import Langlands.Representation.Classification.LanglandsQuotients
import Langlands.Representation.Classification.SegmentConstituentStatement

/-! Products of segment socles are determined by their list of segments. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace SegmentProductDatum

/-- The datum with segment list `l` whose blocks are the canonical segment socles
`T.segmentSocle Δ`. -/
def ofSegmentList (l : List (Segment.{uV, uF} T)) {n : ℕ}
    (hn : (l.map Segment.degree).sum = n) : SegmentProductDatum.{uV, uF} T n where
  length := l.length
  segments := l.get
  degree_sum := by
    rw [← hn, ← List.sum_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map l Segment.degree
  blocks i := T.segmentSocle (l.get i)

theorem ofFn_segments_ofSegmentList (l : List (Segment.{uV, uF} T)) {n : ℕ}
    (hn : (l.map Segment.degree).sum = n) :
    List.ofFn (ofSegmentList l hn).segments = l :=
  List.ofFn_get l

/-- If every segment has a segment socle, the canonical datum of a list has
segment socles. -/
theorem hasSegmentSocles_ofSegmentList
    (hex : Classification.SegmentZelevinskyConstituentExistence.{uF, uV} F T)
    (l : List (Segment.{uV, uF} T)) {n : ℕ} (hn : (l.map Segment.degree).sum = n) :
    (ofSegmentList l hn).HasSegmentSocles := fun i =>
  (hex (l.get i)).choose_spec.1.isSegmentSocle_segmentSocle

/-- Any list of segments is the segment list of a datum with segment socles. -/
theorem exists_of_list
    (hex : Classification.SegmentZelevinskyConstituentExistence.{uF, uV} F T)
    (l : List (Segment.{uV, uF} T)) {n : ℕ} (hn : (l.map Segment.degree).sum = n) :
    ∃ e : SegmentProductDatum.{uV, uF} T n,
      List.ofFn e.segments = l ∧ e.HasSegmentSocles :=
  ⟨ofSegmentList l hn, ofFn_segments_ofSegmentList l hn,
    hasSegmentSocles_ofSegmentList hex l hn⟩

/-- The degrees of the segments of a datum add up to its degree, as a list sum. -/
theorem sum_map_degree_ofFn {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) :
    ((List.ofFn d.segments).map Segment.degree).sum = n := by
  rw [List.map_ofFn, List.sum_ofFn]
  exact d.degree_sum

/-- The sum of the ranks of the segments of a datum, as a list sum. -/
theorem sum_rank_eq {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) :
    ∑ i, (d.segments i).rank = ((List.ofFn d.segments).map Segment.rank).sum := by
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- A datum has two segments, listed as `[Δ, Γ]`, exactly when its length is two
and its segments are `Δ` and `Γ` in this order. -/
theorem ofFn_segments_eq_pair {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (h₂ : d.length = 2) (Δ Γ : Segment.{uV, uF} T) :
    List.ofFn d.segments = [Δ, Γ] ↔
      d.segments ⟨0, by omega⟩ = Δ ∧ d.segments ⟨1, by omega⟩ = Γ := by
  obtain ⟨r, Δs, hs, b⟩ := d
  dsimp only at h₂ ⊢
  subst h₂
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [List.cons.injEq, and_true]
  rfl

/-- Two data with the same list of segments and segment socles induce isomorphic
representations. -/
theorem nonempty_iso_of_ofFn_segments_eq {n : ℕ}
    {d₁ d₂ : SegmentProductDatum.{uV, uF} T n}
    (h : List.ofFn d₁.segments = List.ofFn d₂.segments)
    (h₁ : d₁.HasSegmentSocles) (h₂ : d₂.HasSegmentSocles) :
    Nonempty (d₁.induced ≅ d₂.induced) := by
  obtain ⟨r₁, Δ₁, hs₁, b₁⟩ := d₁
  obtain ⟨r₂, Δ₂, hs₂, b₂⟩ := d₂
  have hr : r₁ = r₂ := by
    simpa only [List.length_ofFn] using congrArg List.length h
  subst hr
  have hΔ : Δ₁ = Δ₂ := List.ofFn_injective h
  subst hΔ
  have e : ∀ i, b₁ i ≅ b₂ i := fun i =>
    (h₁ i).nonempty_iso_segmentSocle.some ≪≫
      (h₂ i).nonempty_iso_segmentSocle.some.symm
  exact ⟨(T.normalizedProductInductionFunctor _).mapIso (Pi.isoMk e)⟩

end SegmentProductDatum

end Langlands.PadicField.TopologicalData
