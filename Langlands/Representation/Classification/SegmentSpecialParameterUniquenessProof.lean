import Langlands.Representation.Classification.SegmentSquareIntegrabilityStatement
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Classification.SegmentIntegralCoordinates
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof

/-! # Uniqueness of the parameter of a special segment head -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

set_option maxHeartbeats 800000 in
/-- An actual irreducible quotient of the increasing segment induction has
the multiset of the segment's members as a supercuspidal support. -/
theorem segmentQuotientCuspidalSupport
    (Δ : T.Segment.{uV, uF})
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentQuotient Δ π) :
    T.IsSupercuspidalSupport π Δ.cuspidalContent := by
  let := T.topology
  obtain ⟨A, hA, hπ, q, hq⟩ := hπ
  let ρ : Fin Δ.length → CuspidalDatum.{uV, uF} T :=
    fun i => Δ.member i.val
  have hr : ∑ i, (ρ i).rank = Δ.degree := by
    simp [ρ, Segment.member, Segment.degree]
  let R : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank) :=
    fun i => SupercuspidalRep.twist
      (T.determinantPowerCharacter Δ.rank (i.val : ℝ))
      (T.isOpen_ker_determinantPowerCharacter _ _)
      (T.ker_determinant_le_ker_determinantPowerCharacter _ _) A
  have hR : ∀ i, (ρ i).IsRepresentedBy (R i) := by
    intro i
    change T.supercuspidalClassRealPowerTwist Δ.rank (i.val : ℝ) A.isoClass =
      T.supercuspidalClassRealPowerTwist Δ.rank (i.val : ℝ) Δ.base.cls
    exact congrArg (T.supercuspidalClassRealPowerTwist _ _) hA
  refine ⟨Δ.length, ρ, rfl, hr, R, hR, hπ, ?_⟩
  change SmoothRep.IsSubquotient π (T.segmentInduced A.obj Δ.length Δ.rank_pos)
  exact SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom q, hq⟩

private theorem support_transport {n m : ℕ} (h : n = m)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (s : Multiset (CuspidalDatum.{uV, uF} T))
    (hs : T.IsSupercuspidalSupport π s) :
    T.IsSupercuspidalSupport (h ▸ π) s := by
  cases h
  exact hs

/-- Isomorphic special heads have the same full segment parameter. -/
theorem segmentSpecialParameterUniqueness :
    SegmentSpecialParameterUniqueness.{uF, uV} F T := by
  let := T.topology
  intro Δ Δ' h π π' hπ hπ' he
  have hs := segmentQuotientCuspidalSupport F T Δ π hπ.isSegmentQuotient
  have hs' := segmentQuotientCuspidalSupport F T Δ' π' hπ'.isSegmentQuotient
  have hπi : π'.IsIrreducible := by
    obtain ⟨A, hA, hi, q, hq⟩ := hπ'.isSegmentQuotient
    exact hi
  have ht : T.IsSupercuspidalSupport (h ▸ π) Δ.cuspidalContent :=
    support_transport F T h π Δ.cuspidalContent hs
  have hc : Δ.cuspidalContent = Δ'.cuspidalContent :=
    Langlands.glSupercuspidalSupportUniqueness.{max uF uV, uF}
      p F T Δ'.degree Δ'.degree_pos π' hπi _ _ (ht.of_iso he.some) hs'
  apply Segment.eq_of_support_eq (cuspidalIntegralTwistFreeness F T)
  ext ρ
  simpa only [← Segment.mem_cuspidalContent] using
    (show ρ ∈ Δ.cuspidalContent ↔ ρ ∈ Δ'.cuspidalContent from by rw [hc])

end Langlands.Classification
