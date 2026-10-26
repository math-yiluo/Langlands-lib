import Langlands.Representation.Classification.SegmentInversionMinimization
import Langlands.Representation.Classification.SegmentProductPermutation

/-! # Actual segment-product embeddings and list inversion reduction

Local representation-theoretic rules remain explicit hypotheses.
-/

noncomputable section

open scoped Classical

namespace Langlands

universe uG uF uV

namespace Classification

/-- If the ambient representation has a strong irreducible socle, every
irreducible embedding into it has the same uniqueness property. -/
theorem IsIrreducibleSocle.of_subrepresentation
    {G : Type uG} [Group G]
    {V W W' : Type uV} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {π : Representation ℂ G W}
    {π' : Representation ℂ G W'}
    (h : IsIrreducibleSocle ρ π)
    (h' : IsIrreducibleSubrepresentation ρ π') :
    IsIrreducibleSocle ρ π' := by
  obtain ⟨hπ, j, hj, huniq⟩ := h
  obtain ⟨hπ', j', hj'⟩ := h'
  refine ⟨hπ', j', hj', ?_⟩
  intro W'' _ _ π'' hπ'' j'' hj''
  exact (huniq W'' π'' hπ'' j'' hj'').trans
    (huniq W' π' hπ' j' hj').symm

end Classification

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace SegmentProductDatum

variable {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)

@[simp] theorem multisegment_degree : d.multisegment.degree = n := by
  simpa [Multisegment.degree, multisegment, List.map_ofFn, List.sum_ofFn]
    using d.degree_sum

/-- The adjacent positions in a displayed list decomposition really lie in
the datum's original finite index type. -/
theorem adjacent_bound_of_list_eq
    {s t : List (Segment.{uV, uF} T)} {Δ Γ : Segment.{uV, uF} T}
    (hl : List.ofFn d.segments = s ++ Δ :: Γ :: t) :
    s.length + 1 < d.length := by
  have hlen := congrArg List.length hl
  simp only [List.length_ofFn, List.length_append, List.length_cons] at hlen
  omega

theorem segment_left_of_list_eq
    {s t : List (Segment.{uV, uF} T)} {Δ Γ : Segment.{uV, uF} T}
    (hl : List.ofFn d.segments = s ++ Δ :: Γ :: t) :
    d.segments ⟨s.length, by have := d.adjacent_bound_of_list_eq hl; omega⟩ = Δ := by
  have hget : (List.ofFn d.segments)[s.length]'(by
      simpa using Nat.lt_trans (Nat.lt_succ_self _) (d.adjacent_bound_of_list_eq hl)) = Δ := by
    simp [hl]
  simpa using hget

theorem segment_right_of_list_eq
    {s t : List (Segment.{uV, uF} T)} {Δ Γ : Segment.{uV, uF} T}
    (hl : List.ofFn d.segments = s ++ Δ :: Γ :: t) :
    d.segments ⟨s.length + 1, d.adjacent_bound_of_list_eq hl⟩ = Γ := by
  have hget : (List.ofFn d.segments)[s.length + 1]'(by
      simpa using d.adjacent_bound_of_list_eq hl) = Γ := by
    simp [hl]
  simpa using hget

/-- An indexed adjacent permutation swaps precisely the displayed pair.
Outside occurrences, including equal-valued segments, keep their positions. -/
theorem ofFn_permute_adjacentSwap_of_list_eq
    {s t : List (Segment.{uV, uF} T)} {Δ Γ : Segment.{uV, uF} T}
    (hl : List.ofFn d.segments = s ++ Δ :: Γ :: t) :
    List.ofFn
        (d.permute (d.shape.adjacentSwap s.length (d.adjacent_bound_of_list_eq hl))).segments =
      s ++ Γ :: Δ :: t := by
  have hlen := congrArg List.length hl
  simp only [List.length_ofFn, List.length_append, List.length_cons] at hlen
  change List.ofFn (fun i : Fin d.length =>
    d.segments (Equiv.swap
      (⟨s.length, by have := d.adjacent_bound_of_list_eq hl; omega⟩ : Fin d.length)
      ⟨s.length + 1, d.adjacent_bound_of_list_eq hl⟩ i)) = _
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons]
    omega
  · intro k hk hk'
    simp only [List.getElem_ofFn]
    by_cases hka : k = s.length
    · subst k
      rw [Equiv.swap_apply_left, d.segment_right_of_list_eq hl]
      simp
    · by_cases hkb : k = s.length + 1
      · subst k
        rw [Equiv.swap_apply_right, d.segment_left_of_list_eq hl]
        simp
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · have hget : d.segments ⟨k, by simpa using hk⟩ =
              (s ++ Δ :: Γ :: t)[k]'(by
                simp only [List.length_append, List.length_cons]
                have : k < d.length := by simpa using hk
                omega) := by
            simp [← hl]
          rw [hget]
          by_cases hks : k < s.length
          · simp [hks]
          · have hkt : 2 ≤ k - s.length := by omega
            simp [List.getElem_append, hks, List.getElem_cons, show k - s.length ≠ 0 by omega,
              show k - s.length - 1 ≠ 0 by omega]
        · simpa only [ne_eq, Fin.ext_iff] using hka
        · simpa only [ne_eq, Fin.ext_iff] using hkb

/-- An actual irreducible embedding into a product of actual segment socles.
The datum need not be ordered. -/
def HasSocleEmbedding
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  d.HasSegmentSocles ∧
    Classification.IsIrreducibleSubrepresentation d.induced.representation π.representation

end SegmentProductDatum

/-- Lists realized by genuine segment-socle product data carrying the given
irreducible embedding. The fixed rank and all actual blocks are retained. -/
def SocleEmbeddingList {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (l : List (Segment.{uV, uF} T)) : Prop :=
  ∃ d : SegmentProductDatum.{uV, uF} T n,
    List.ofFn d.segments = l ∧ d.HasSocleEmbedding π

/-- The actual indexed local rules required to apply inversion minimization
to an embedding. These rules are specified here, not proved. -/
def HasIndexedSocleEmbeddingReductions {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  (∀ (d : SegmentProductDatum.{uV, uF} T n) (j : ℕ) (h : j + 1 < d.length),
    ¬ (d.segments ⟨j, by omega⟩).IsLinked (d.segments ⟨j + 1, h⟩) →
      d.HasSocleEmbedding π →
        (d.permute (d.shape.adjacentSwap j h)).HasSocleEmbedding π) ∧
  (∀ (d : SegmentProductDatum.{uV, uF} T n) (j : ℕ) (h : j + 1 < d.length),
    (d.segments ⟨j, by omega⟩).Precedes (d.segments ⟨j + 1, h⟩) →
      d.HasSocleEmbedding π →
        (d.permute (d.shape.adjacentSwap j h)).HasSocleEmbedding π ∨
          ∃ (U : Segment.{uV, uF} T) (I : Option (Segment.{uV, uF} T))
            (e : SegmentProductDatum.{uV, uF} T n),
            Segment.IsUnionIntersectionReplacement
              (d.segments ⟨j, by omega⟩) (d.segments ⟨j + 1, h⟩) U I ∧
            List.ofFn e.segments =
              (List.ofFn d.segments).take j ++ [U] ++ I.toList ++
                (List.ofFn d.segments).drop (j + 2) ∧
            e.HasSocleEmbedding π)

/-- Indexed local rules for actual data induce the list rules without
forgetting rank, multiplicity, actual blocks, or the embedding. -/
theorem HasIndexedSocleEmbeddingReductions.hasLocalSegmentReductions {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hlocal : HasIndexedSocleEmbeddingReductions.{uF, uV} π) :
    HasLocalSegmentReductions (SocleEmbeddingList.{uF, uV} π) := by
  constructor
  · intro s t Δ Γ hu hl
    obtain ⟨d, hd, hembed⟩ := hl
    have hb := d.adjacent_bound_of_list_eq hd
    have hu' :
        ¬ (d.segments ⟨s.length, by omega⟩).IsLinked
          (d.segments ⟨s.length + 1, hb⟩) := by
      simpa only [d.segment_left_of_list_eq hd, d.segment_right_of_list_eq hd] using hu
    exact ⟨d.permute (d.shape.adjacentSwap s.length hb),
      d.ofFn_permute_adjacentSwap_of_list_eq hd, hlocal.1 d s.length hb hu' hembed⟩
  · intro s t Δ Γ hp hl
    obtain ⟨d, hd, hembed⟩ := hl
    have hb := d.adjacent_bound_of_list_eq hd
    have hp' :
        (d.segments ⟨s.length, by omega⟩).Precedes
          (d.segments ⟨s.length + 1, hb⟩) := by
      simpa only [d.segment_left_of_list_eq hd, d.segment_right_of_list_eq hd] using hp
    rcases hlocal.2 d s.length hb hp' hembed with hswap | ⟨U, I, e, hs, he, hembed'⟩
    · exact Or.inl ⟨d.permute (d.shape.adjacentSwap s.length hb),
        d.ofFn_permute_adjacentSwap_of_list_eq hd, hswap⟩
    · refine Or.inr ⟨U, I, ?_, e, ?_, hembed'⟩
      · simpa only [d.segment_left_of_list_eq hd, d.segment_right_of_list_eq hd] using hs
      · have htake : (List.ofFn d.segments).take s.length = s := by simp [hd]
        have hdrop : (List.ofFn d.segments).drop (s.length + 2) = t := by
          simp [hd, List.drop_append]
        simpa only [htake, hdrop, List.append_assoc, List.singleton_append] using he

/-- An inhabited collection of actual embedding data satisfying the indexed
rules contains actual ordered embedding data. All local rules and freeness
are explicit premises. -/
theorem HasIndexedSocleEmbeddingReductions.exists_ordered {n : ℕ}
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hlocal : HasIndexedSocleEmbeddingReductions.{uF, uV} π)
    (hne : ∃ d : SegmentProductDatum.{uV, uF} T n, d.HasSocleEmbedding π) :
    ∃ d : SegmentProductDatum.{uV, uF} T n,
      d.IsPrecedenceOrdered ∧ d.HasSocleEmbedding π := by
  have hlist : ∃ l, SocleEmbeddingList.{uF, uV} π l := by
    obtain ⟨d, hd⟩ := hne
    exact ⟨List.ofFn d.segments, d, rfl, hd⟩
  obtain ⟨l, ⟨d, hd, hembed⟩, ho⟩ :=
    hlocal.hasLocalSegmentReductions.exists_ordered hfree hlist
  refine ⟨d, ?_, hembed⟩
  exact (T.isPrecedenceOrdered_iff_list d.segments).mpr (by simpa only [hd] using ho)

namespace SegmentProductDatum

/-- Once ordered-product strong-socle existence is supplied, the actual
irreducible embedding already constructed has the strong socle relation. -/
theorem HasSocleEmbedding.isZelevinskySocle_of_exists {n : ℕ}
    {d : SegmentProductDatum.{uV, uF} T n}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.HasSocleEmbedding π)
    (hs : ∃ σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      d.IsZelevinskySocle σ) :
    d.IsZelevinskySocle π := by
  obtain ⟨σ, ho, _, hs⟩ := hs
  exact ⟨ho, h.1, hs.of_subrepresentation h.2⟩

end SegmentProductDatum

end PadicField.TopologicalData

end Langlands
