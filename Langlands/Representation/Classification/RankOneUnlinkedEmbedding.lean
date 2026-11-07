import Langlands.Representation.Classification.RankOneSegmentHom
import Langlands.Representation.Classification.GenericSegmentProductExhaustionProof
import Langlands.Representation.Classification.UnlinkedCuspidalContentInjectivityProof
import Langlands.Representation.Classification.UnlinkedSegmentSocleProductIrreducibleProof
import Langlands.Representation.Classification.SegmentSocleProductComparison
import Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof

/-! Unlinked segment-socle embeddings into weakly ordered rank-one principal series. -/

noncomputable section

namespace Langlands.Classification.RankOneUnlinkedEmbedding

open GeneralLinear PadicField.TopologicalData RankOneSegmentHom

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem irreducible_of_unlinked {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{uV, uF} n) (hsoc : d.HasSegmentSocles)
    (hu : d.multisegment.IsUnlinked) :
    letI := T.topology
    d.induced.IsIrreducible := by
  cases n with
  | zero => omega
  | succ n => exact unlinkedSegmentSocleProductIrreducible F T n d hsoc hu

set_option maxHeartbeats 1200000 in
/-- A principal series with weakly decreasing scalar norms contains an actual
irreducible unlinked product of rank-one segment socles with the same content. -/
theorem exists_unlinked_embedding
    {m : ℕ} (hm : 0 < m)
    (X : letI := T.topology;
      Fin m → SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := 1))
    (horder : Antitone (fun t => (rankOneDatum F T (X t)).scalarUniformizerNorm)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m * 1)
    ∃ d : T.SegmentProductDatum.{uV, uF} (m * 1),
      d.HasSegmentSocles ∧ d.multisegment.IsUnlinked ∧
      (∀ j, (d.segments j).rank = 1) ∧
      d.multisegment.cuspidalContent = List.ofFn (fun t => rankOneDatum F T (X t)) ∧
      IsIrreducibleSubrepresentation
        (T.normalizedProductInduced (BlockShape.uniform m 1 Nat.one_pos)
          (fun t => (X t).obj.representation)) d.induced.representation := by
  classical
  let := T.topology
  let := T.generalLinearTopologicalGroup (m * 1)
  let content : Multiset (CuspidalDatum.{uV, uF} T) :=
    List.ofFn (fun t => rankOneDatum F T (X t))
  obtain ⟨a, hu, hcontent⟩ := Multisegment.exists_unlinked_of_cuspidalContent
    (cuspidalIntegralTwistFreeness F T) content
  have hrank (Δ : Segment.{uV, uF} T) (hΔ : Δ ∈ a) : Δ.rank = 1 := by
    have hb := (Multisegment.mem_cuspidalContent_iff a Δ.base).mpr
      ⟨Δ, hΔ, Δ.base_mem_support⟩
    rw [hcontent] at hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hb)
    exact (congrArg CuspidalDatum.rank hi).symm
  have hdegree : a.degree = m * 1 := by
    rw [← Multisegment.sum_rank_cuspidalContent, hcontent]
    simp [content, rankOneDatum, List.map_ofFn, Function.comp_def]
  have hlist : (a.toList.map Segment.degree).sum = m * 1 := by
    calc
      _ = ((↑a.toList : Multiset (Segment.{uV, uF} T)).map Segment.degree).sum := by
        simp only [Multiset.map_coe, Multiset.sum_coe]
      _ = a.degree := by rw [Multiset.coe_toList]; rfl
      _ = m * 1 := hdegree
  let d := SegmentProductDatum.ofSegmentList a.toList hlist
  have hmult : d.multisegment = a := by
    change (List.ofFn d.segments : Multiset (Segment.{uV, uF} T)) = a
    rw [SegmentProductDatum.ofFn_segments_ofSegmentList, Multiset.coe_toList]
  have hsoc : d.HasSegmentSocles := SegmentProductDatum.hasSegmentSocles_ofSegmentList
    (segmentZelevinskyConstituentExistence F T) a.toList hlist
  have hu' : d.multisegment.IsUnlinked := hmult.symm ▸ hu
  have hrank' : ∀ j, (d.segments j).rank = 1 := fun j => hrank _ (by
    rw [← hmult]
    exact Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩))
  have hcontent' : d.multisegment.cuspidalContent = List.ofFn (fun t => rankOneDatum F T (X t)) := by
    rw [hmult]
    exact hcontent
  let f := inductionMapOfContent F T hm d hrank' hsoc X hcontent' horder
  have hi := irreducible_of_unlinked F T (Nat.mul_pos hm Nat.one_pos) d hsoc hu'
  let := hi
  have hf : Function.Injective f.val :=
    (Representation.IsIrreducible.injective_or_eq_zero f.val).resolve_right f.property
  exact ⟨d, hsoc, hu', hrank', hcontent', hi, f.val, hf⟩

/-- A chosen segment product, with its socle, content, unlinkedness and actual
irreducible-embedding witnesses, for the weakly ordered target tuple. -/
def unlinkedEmbeddingDatum
    {m : ℕ} (hm : 0 < m)
    (X : letI := T.topology;
      Fin m → SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := 1))
    (horder : Antitone (fun t => (rankOneDatum F T (X t)).scalarUniformizerNorm)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m * 1)
    { d : T.SegmentProductDatum.{uV, uF} (m * 1) //
      d.HasSegmentSocles ∧ d.multisegment.IsUnlinked ∧
      (∀ j, (d.segments j).rank = 1) ∧
      d.multisegment.cuspidalContent = List.ofFn (fun t => rankOneDatum F T (X t)) ∧
      IsIrreducibleSubrepresentation
        (T.normalizedProductInduced (BlockShape.uniform m 1 Nat.one_pos)
          (fun t => (X t).obj.representation)) d.induced.representation } :=
  Classical.indefiniteDescription _ (exists_unlinked_embedding F T hm X horder)

end Langlands.Classification.RankOneUnlinkedEmbedding
