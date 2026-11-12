import Langlands.Representation.Classification.SpehIntegralLineSupportStatement
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.SegmentHeadProductCuspidalQuotient

/-! # Speh cuspidal support on one integral twist line -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Classify the square-integrable block by a segment, then compose the
actual cuspidal quotient of the centered segment-head product with the
supplied Speh quotient. -/
theorem spehIntegralLineSupport : SpehIntegralLineSupport.{uF, uV} F T := by
  let := T.topology
  intro d S hS
  rcases d with ⟨r, hr, k, hk, δ⟩
  obtain ⟨Δ, he, hΔ⟩ :=
    (segmentEssentialSquareIntegrableClassification.{uF, uV} F T r hr δ hS.1.1).mp
      hS.1.2.2.isEssentiallySquareIntegrable
  cases he
  let d : SpehDatum.{uF, uV} F T := ⟨Δ.degree, hr, k, hk, δ⟩
  let E : T.SegmentProductDatum.{max uF uV, uF} d.degree := {
    length := k
    segments := fun i => Δ.twist (d.exponent i)
    degree_sum := by
      change ∑ _i : Fin k, Δ.degree = k * Δ.degree
      simp
    blocks := fun i => T.segmentFactor δ (d.exponent i) }
  have hE : E.HasSegmentHeads := by
    intro i
    exact ((segmentConstituentRealTwistCompatibility.{uF, max uF uV} F T
      Δ (d.exponent i) δ).2.1).mp hΔ
  have hind : E.induced = d.centeredInduced := rfl
  let C := segmentHeadProductCuspidalQuotient T E hE
  obtain ⟨hSi, q, hq⟩ := hS.2.1
  have hs : T.IsSupercuspidalSupport S E.multisegment.cuspidalContent := by
    refine ⟨C.length, C.members, C.content_eq, C.rank_sum, C.representatives,
      C.represents, hSi, ?_⟩
    apply SmoothRep.IsQuotient.isSubquotient
    refine ⟨C.quotientMap ≫ SmoothRep.ofHom q, ?_⟩
    exact hq.comp C.surjective
  refine ⟨Δ.base.twist (((k : ℝ) - 1) / 2), E.multisegment.cuspidalContent, hs, ?_⟩
  intro τ hτ
  change τ ∈ Multiset.join _ at hτ
  simp only [SegmentProductDatum.multisegment, Multiset.mem_join,
    Multiset.mem_map, Multiset.mem_coe, List.mem_ofFn] at hτ
  obtain ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, hτ⟩ := hτ
  rw [Segment.mem_cuspidalContent] at hτ
  obtain ⟨j, hj, hτ⟩ := hτ
  refine ⟨(j : ℤ) - (i.val : ℤ), ?_⟩
  rw [← hτ]
  simp only [E, Segment.member, Segment.twist, CuspidalDatum.twist_twist,
    Int.cast_sub, Int.cast_natCast]
  congr 1
  dsimp [d, SpehDatum.exponent]
  ring

end Langlands.Classification
