import Langlands.AllFieldBZ.Representation.Classification.SegmentHeadExistenceStatement
import Langlands.AllFieldBZ.Representation.Classification.SegmentSocleExistenceStatement
import Langlands.Representation.Aubert.LocalFieldGradedGrothendieck
import Langlands.Representation.Aubert.LocalFieldSupportSign
import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Classification.Segments

/-! Actual segment endpoint classes for arbitrary nonarchimedean local fields. -/

noncomputable section

namespace Langlands.Aubert.LocalFieldGraded

open CategoryTheory GeneralLinear
open AllFieldBZ.LocalFieldPackage.TopologicalData
open AllFieldBZ.Classification (SegmentSocleExistenceStatement SegmentHeadExistenceStatement)

universe uF uV

variable {K : AllFieldBZ.LocalFieldPackage.{uF}} (T : K.TopologicalData)

section Support

variable (Δ : Segment.{max uF uV, uF} T)
  (π : letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree K.Carrier))

/-- The support multiset given by the members of the segment. -/
def segmentSupport : Multiset (CuspidalDatum.{max uF uV,uF} T) :=
  List.ofFn (fun i : Fin Δ.length => Δ.member i)

theorem segmentSupport_card : (segmentSupport T Δ).card = Δ.length := by
  simp [segmentSupport]

theorem segmentSocle_hasSupport (hZ : T.IsSegmentSocle Δ π) :
    T.IsSupercuspidalSupport π (segmentSupport T Δ) := by
  let := T.topology
  obtain ⟨A, hA, hi, j, hj, -⟩ := hZ
  refine ⟨Δ.length, fun i => Δ.member i, rfl, by simp [Segment.member, Nat.mul_comm],
    T.segmentFactor Δ A, T.segmentFactor_isRepresentedBy Δ hA, hi, ?_⟩
  exact SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom j, hj⟩

theorem segmentSpecial_hasSupport (hS : T.IsSegmentHead Δ π) :
    T.IsSupercuspidalSupport π (segmentSupport T Δ) := by
  let := T.topology
  obtain ⟨A, hA, hi, q, hq, -⟩ := hS
  refine ⟨Δ.length, fun i => Δ.member i, rfl, by simp [Segment.member, Nat.mul_comm],
    T.segmentFactor Δ A, T.segmentFactor_isRepresentedBy Δ hA, hi, ?_⟩
  exact SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom q, hq⟩

theorem supportSign_of_segmentSupport (hπ : letI := T.topology; π.IsIrreducible)
    (h : T.IsSupercuspidalSupport π (segmentSupport T Δ)) :
    letI := T.topology
    supportSign T Δ.degree (SmoothRep.irreducibleIsoClass π hπ) =
      (-1 : ℤ) ^ (Δ.degree - Δ.length) := by
  let := T.topology
  rw [supportSign_of_support T π hπ _ h, segmentSupport_card]

end Support

section Classes

variable (Δ : Segment.{max uF uV,uF} T)

/-- The actual irreducible socle of the increasing segment product,
chosen from the segment socle existence property. -/
def segmentSocleObject (h : SegmentSocleExistenceStatement.{uF,max uF uV} K T) :
    letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree K.Carrier) :=
  Classical.choose (h Δ)

theorem segmentSocleObject_spec (h : SegmentSocleExistenceStatement.{uF,max uF uV} K T) :
    T.IsSegmentSocle Δ (segmentSocleObject T Δ h) :=
  Classical.choose_spec (h Δ)

/-- The actual irreducible head of the increasing segment product,
chosen from the special constituent existence property. -/
def segmentSpecialObject (h : SegmentHeadExistenceStatement.{uF,max uF uV} K T) :
    letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree K.Carrier) :=
  Classical.choose (h Δ)

theorem segmentSpecialObject_spec (h : SegmentHeadExistenceStatement.{uF,max uF uV} K T) :
    T.IsSegmentHead Δ (segmentSpecialObject T Δ h) :=
  Classical.choose_spec (h Δ)

/-- The rank-homogeneous exact Grothendieck class of the actual segment socle. -/
def segmentSocleClass (h : SegmentSocleExistenceStatement.{uF,max uF uV} K T) :
    letI := T.topology
    FiniteLengthGrothendieckGroup.{uV,uF} Δ.degree K.Carrier :=
  letI := T.topology
  finiteLengthClass Δ.degree K.Carrier (segmentSocleObject T Δ h)
    (SmoothRep.hasFiniteLength_of_isIrreducible (by
      obtain ⟨_, _, hs⟩ := segmentSocleObject_spec T Δ h
      exact hs.1))

/-- The rank-homogeneous exact Grothendieck class of the actual special head. -/
def segmentSpecialClass (h : SegmentHeadExistenceStatement.{uF,max uF uV} K T) :
    letI := T.topology
    FiniteLengthGrothendieckGroup.{uV,uF} Δ.degree K.Carrier :=
  letI := T.topology
  finiteLengthClass Δ.degree K.Carrier (segmentSpecialObject T Δ h)
    (SmoothRep.hasFiniteLength_of_isIrreducible (by
      obtain ⟨_, _, hs⟩ := segmentSpecialObject_spec T Δ h
      exact hs.1))

variable (π : letI := T.topology
  SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree K.Carrier))

/-- Any actual segment socle has the chosen exact class. -/
theorem segmentSocleClass_of_object (h : SegmentSocleExistenceStatement.{uF,max uF uV} K T)
    (hπ : T.IsSegmentSocle Δ π) (hl : letI := T.topology; π.HasFiniteLength) :
    letI := T.topology
    segmentSocleClass.{uF,uV} T Δ h = finiteLengthClass Δ.degree K.Carrier π hl := by
  let := T.topology
  obtain ⟨A, hA, hZ⟩ := segmentSocleObject_spec T Δ h
  obtain ⟨B, hB, hπ⟩ := hπ
  let e := SmoothRep.equivOfIso (T.segmentInducedIsoOfRepresented Δ hB hA)
  obtain ⟨eZ⟩ := hZ.nonempty_socleEquiv
  obtain ⟨eπ⟩ := (hπ.of_equiv e).nonempty_socleEquiv
  exact SmoothRep.FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
    (SmoothRep.mkIso (eZ.trans eπ.symm))

/-- Any actual special head has the chosen exact class. -/
theorem segmentSpecialClass_of_object (h : SegmentHeadExistenceStatement.{uF,max uF uV} K T)
    (hπ : T.IsSegmentHead Δ π) (hl : letI := T.topology; π.HasFiniteLength) :
    letI := T.topology
    segmentSpecialClass.{uF,uV} T Δ h = finiteLengthClass Δ.degree K.Carrier π hl := by
  let := T.topology
  obtain ⟨A, hA, hS⟩ := segmentSpecialObject_spec T Δ h
  obtain ⟨B, hB, hπ⟩ := hπ
  let e := SmoothRep.equivOfIso (T.segmentInducedIsoOfRepresented Δ hB hA)
  obtain ⟨eS⟩ := hS.nonempty_headEquiv
  obtain ⟨eπ⟩ := (hπ.of_equiv e).nonempty_headEquiv
  exact SmoothRep.FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
    (SmoothRep.mkIso (eS.symm.trans eπ))

end Classes

end Langlands.Aubert.LocalFieldGraded
