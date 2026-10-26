import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Classification.SegmentSocleInversionReduction
import Langlands.Representation.Classification.SupercuspidalEmbeddingProof

/-! Every irreducible representation embeds into an actual product of segment socles. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The collection of actual segment-socle product embeddings is nonempty,
including at rank zero. No order or full-product socle uniqueness is asserted. -/
theorem exists_segmentSocleEmbedding {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible) :
    ∃ d : SegmentProductDatum.{max uF uV, uF} T n, d.HasSocleEmbedding π := by
  let := T.topology
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨_, j, hj, _⟩ :=
      (Classification.emptySegmentProduct_isZelevinskySocle F T π hπ).2.2
    exact ⟨.empty, SegmentProductDatum.empty_hasSegmentSocles, hπ, j, hj⟩
  · obtain ⟨_, ρ, hρ⟩ :=
      Langlands.glSupercuspidalEmbedding.{max uF uV, uF} p F T n hn π hπ
    exact IsCuspidalSubrepresentation.exists_segmentSocleProduct T hρ

/-- Choose actual segment-socle product data carrying the given irreducible
embedding. The existence theorem supplies every representation-theoretic input. -/
def socleEmbeddingDatum {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible) :
    SegmentProductDatum.{max uF uV, uF} T n :=
  Classical.choose (T.exists_segmentSocleEmbedding π hπ)

/-- The chosen actual datum retains the segment socles and the actual full-product embedding. -/
theorem socleEmbeddingDatum_hasSocleEmbedding {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible) :
    (T.socleEmbeddingDatum π hπ).HasSocleEmbedding π :=
  Classical.choose_spec (T.exists_segmentSocleEmbedding π hπ)

end Langlands.PadicField.TopologicalData
