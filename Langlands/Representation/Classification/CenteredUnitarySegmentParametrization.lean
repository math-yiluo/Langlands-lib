import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.SegmentCenteredSpecialSquareIntegrabilityProof
import Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof

/-!
# Centered unitary segment parameters on the supplied action

For a square-integrable segment head, real unitarization of its supercuspidal
base must occur at the segment midpoint. This gives an actual unitary base
representative without replacing the supplied head or its carrier.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The midpoint twist of the base of an actual square-integrable segment head
has an actual unitarizable supercuspidal representative. -/
theorem exists_unitaryMidpointBase_of_isSquareIntegrable_segmentHead
    (Δ : T.Segment.{max uF uV, uF})
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hhead : T.IsSegmentHead Δ π)
    (hsi : letI := T.topology
      T.IsSquareIntegrable π.representation) :
    letI := T.topology
    ∃ A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := Δ.rank),
      (Δ.twist (((Δ.length : ℝ) - 1) / 2)).base.IsRepresentedBy A ∧
        IsUnitarizable A.obj.representation := by
  let := T.topology
  let A := hhead.choose
  have hA : Δ.base.IsRepresentedBy A := hhead.choose_spec.1
  obtain ⟨t, ht, _⟩ :=
    supercuspidalRepRealUnitarization F T Δ.rank Δ.rank_pos A
  let At := SupercuspidalRep.twist (T.determinantPowerCharacter Δ.rank t)
    (T.isOpen_ker_determinantPowerCharacter Δ.rank t)
    (T.ker_determinant_le_ker_determinantPowerCharacter Δ.rank t) A
  have hAt : (Δ.twist t).base.IsRepresentedBy At := by
    change T.supercuspidalClassRealPowerTwist Δ.rank t A.isoClass =
      T.supercuspidalClassRealPowerTwist Δ.rank t Δ.base.cls
    exact congrArg (T.supercuspidalClassRealPowerTwist Δ.rank t) hA
  have hheadt := (segmentConstituentRealTwistCompatibility.{uF, max uF uV}
    F T Δ t π).2.1.mp hhead
  have hc := (segmentCenteredSpecialSquareIntegrability.{uF, uV}
    F T (Δ.twist t) At hAt ht (T.segmentFactor π t)
      hheadt.isSegmentQuotient).1
  let m : ℝ := ((Δ.length : ℝ) - 1) / 2
  change T.IsSquareIntegrable
    (realPowerTwist (T.determinantNorm Δ.degree) (-m)
      (realPowerTwist (T.determinantNorm Δ.degree) t π.representation)) at hc
  rw [← realPowerTwist_add] at hc
  have harith : -m + t = -(m - t) := by ring
  rw [harith] at hc
  have hzero : T.IsSquareIntegrable
      (realPowerTwist (T.determinantNorm Δ.degree) (-(0 : ℝ)) π.representation) := by
    simpa only [neg_zero, realPowerTwist_zero] using hsi
  obtain ⟨v, hv⟩ := FiniteIndexRestriction.exists_ne_zero π.representation
    hhead.isSegmentQuotient.choose_spec.2.1
  have he : m - t = 0 := exponent_eq_of_isSquareIntegrable Δ.degree_pos hv hc hzero
  have hmid : t = m := by linarith
  refine ⟨At, ?_, ht⟩
  exact (congrArg (fun s : ℝ => (Δ.twist s).base.IsRepresentedBy At) hmid).mp hAt

/-- Every supplied positive-rank irreducible square-integrable representation
has a strong segment-head description whose midpoint base is unitarizable. -/
theorem exists_segmentHead_unitaryMidpointBase_of_isSquareIntegrable
    (n : ℕ) (hn : 0 < n)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hi : letI := T.topology
      Representation.IsIrreducible π.representation)
    (hsi : letI := T.topology
      T.IsSquareIntegrable π.representation) :
    letI := T.topology
    ∃ (Δ : T.Segment.{max uF uV, uF}) (h : Δ.degree = n)
      (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := Δ.rank)),
      T.IsSegmentHead Δ (h.symm ▸ π) ∧
        (Δ.twist (((Δ.length : ℝ) - 1) / 2)).base.IsRepresentedBy A ∧
          IsUnitarizable A.obj.representation := by
  let := T.topology
  have hess : T.IsEssentiallySquareIntegrable π.representation :=
    ⟨0, by simpa only [neg_zero, realPowerTwist_zero] using hsi⟩
  obtain ⟨Δ, h, hhead⟩ :=
    (segmentEssentialSquareIntegrableClassification.{uF, uV} F T n hn π hi).mp hess
  have hsΔ : T.IsSquareIntegrable (h.symm ▸ π).representation := by
    cases h
    exact hsi
  obtain ⟨A, hA, hu⟩ := exists_unitaryMidpointBase_of_isSquareIntegrable_segmentHead
    F T Δ (h.symm ▸ π) hhead hsΔ
  exact ⟨Δ, h, A, hhead, hA, hu⟩

/-- A centered description with an actual unitary supercuspidal base: the
positive midpoint twist of the supplied action is the strong segment head. -/
theorem exists_centeredUnitarySegmentHead_of_isSquareIntegrable
    (n : ℕ) (hn : 0 < n)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hi : letI := T.topology
      Representation.IsIrreducible π.representation)
    (hsi : letI := T.topology
      T.IsSquareIntegrable π.representation) :
    letI := T.topology
    ∃ (Δ : T.Segment.{max uF uV, uF}) (h : Δ.degree = n)
      (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := Δ.rank)),
      Δ.base.IsRepresentedBy A ∧ IsUnitarizable A.obj.representation ∧
        T.IsSegmentHead Δ
          (T.segmentFactor (h.symm ▸ π) (((Δ.length : ℝ) - 1) / 2)) := by
  let := T.topology
  obtain ⟨Δ, h, A, hhead, hA, hu⟩ :=
    exists_segmentHead_unitaryMidpointBase_of_isSquareIntegrable F T n hn π hi hsi
  refine ⟨Δ.twist (((Δ.length : ℝ) - 1) / 2), h, A, hA, hu, ?_⟩
  exact (segmentConstituentRealTwistCompatibility.{uF, max uF uV}
    F T Δ (((Δ.length : ℝ) - 1) / 2) (h.symm ▸ π)).2.1.mp hhead

/-- A segment description of the supplied action, with an actual unitary
supercuspidal representative for its midpoint-twisted base. -/
structure SquareIntegrableSegmentParameter (n : ℕ)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) where
  segment : T.Segment.{max uF uV, uF}
  degree_eq : segment.degree = n
  base : letI := T.topology
    SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := segment.rank)
  base_repr : (segment.twist (((segment.length : ℝ) - 1) / 2)).base.IsRepresentedBy base
  unitarizable : letI := T.topology
    IsUnitarizable base.obj.representation
  head : T.IsSegmentHead segment (degree_eq.symm ▸ π)

/-- Choose the segment parameters on the supplied square-integrable action. -/
def squareIntegrableSegmentParameter (n : ℕ) (hn : 0 < n)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hi : letI := T.topology
      Representation.IsIrreducible π.representation)
    (hsi : letI := T.topology
      T.IsSquareIntegrable π.representation) :
    SquareIntegrableSegmentParameter F T n π :=
  Classical.choice (by
    obtain ⟨Δ, h, A, hh, hA, hu⟩ :=
      exists_segmentHead_unitaryMidpointBase_of_isSquareIntegrable F T n hn π hi hsi
    exact ⟨⟨Δ, h, A, hA, hu, hh⟩⟩)

end Langlands.Classification
