import Langlands.Representation.Classification.SpehSegmentParameters
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof

/-! # Actual Speh quotients as rectangular multisegment quotients -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Centering at the midpoint of an arbitrary segment recovers that segment. -/
theorem tadicCenteredSegment_midpoint (Δ : T.Segment.{uV, uF}) :
    tadicCenteredSegment (Δ.base.twist (((Δ.length : ℝ) - 1) / 2))
      Δ.length Δ.length_pos 0 = Δ := by
  cases Δ
  simp [tadicCenteredSegment, CuspidalDatum.twist_twist]

namespace SpehDatum

/-- The actual segment product has precisely the centered rectangular label. -/
theorem segmentProductDatum_centered_multisegment (d : SpehDatum.{uF, uV} F T)
    (Δ : T.Segment.{max uF uV, uF}) (h : Δ.degree = d.rank) :
    (d.segmentProductDatum Δ h).multisegment =
      tadicMultisegment (Δ.base.twist (((Δ.length : ℝ) - 1) / 2))
        d.length Δ.length Δ.length_pos := by
  rcases d with ⟨r, hr, k, hk, δ⟩
  change Δ.degree = r at h
  cases h
  let d : SpehDatum.{uF, uV} F T := ⟨Δ.degree, hr, k, hk, δ⟩
  have hs := spehSegments_multiset
    (Δ.base.twist (((Δ.length : ℝ) - 1) / 2)) Δ.length d.length Δ.length_pos
  unfold Langlands.Classification.spehSegments at hs
  rw [tadicCenteredSegment_midpoint] at hs
  exact hs

/-- The supplied Speh quotient itself is a weak multisegment Langlands quotient. -/
theorem isLanglandsQuotient_segmentProductDatum (d : SpehDatum.{uF, uV} F T)
    (Δ : T.Segment.{max uF uV, uF}) (h : Δ.degree = d.rank)
    (hδ : T.IsSegmentHead Δ (h.symm ▸ d.delta))
    (S : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
    (hS : d.IsSpeh S) : (d.segmentProductDatum Δ h).IsLanglandsQuotient S := by
  let := T.topology
  refine ⟨d.segmentProductDatum_isPrecedenceOrdered Δ h,
    d.segmentProductDatum_hasSegmentHeads Δ h hδ, ?_⟩
  rw [d.segmentProductDatum_induced]
  exact hS.2.1

/-- Square-integrable classification supplies a common segment for every Speh
length built from the supplied discrete-series action. -/
theorem exists_segmentHead (d : SpehDatum.{uF, uV} F T) (hd : d.IsDiscreteSeries) :
    ∃ (Δ : T.Segment.{max uF uV, uF}) (h : Δ.degree = d.rank),
      T.IsSegmentHead Δ (h.symm ▸ d.delta) := by
  let := T.topology
  exact (segmentEssentialSquareIntegrableClassification.{uF, uV}
    F T d.rank d.rank_pos d.delta hd.1).mp hd.2.2.isEssentiallySquareIntegrable

end SpehDatum

end Langlands.Classification
