import Langlands.Representation.Aubert.GradedGrothendieck
import Langlands.Representation.Aubert.SegmentSocleHeadProof
import Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof
import Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
import Langlands.Representation.Classification.CanonicalConstituents

/-!
# Actual segment objects and their graded exact-K0 classes

The two chosen objects are actual strong constituents of the increasing
segment induction. Their identification with any supplied strong constituent
is an actual representation equivalence, before passing to exact K0.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An actual strong segment socle chosen from published constituent existence. -/
def segmentSocleObject (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier) :=
  letI := T.topology
  Classical.choose
    (Classification.segmentZelevinskyConstituentExistence.{uF, max uF uV} F T Δ)

theorem segmentSocleObject_spec (Δ : T.Segment.{max uF uV, uF}) :
    T.IsSegmentSocle Δ (segmentSocleObject F T Δ) :=
  (Classical.choose_spec
    (Classification.segmentZelevinskyConstituentExistence.{uF, max uF uV} F T Δ)).1

/-- The actual special quotient, the strong head of the increasing product. -/
def segmentSpecialObject (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier) :=
  letI := T.topology
  Classical.choose
    (Classification.segmentSpecialConstituentExistence.{uF, max uF uV} F T Δ)

theorem segmentSpecialObject_spec (Δ : T.Segment.{max uF uV, uF}) :
    T.IsSegmentHead Δ (segmentSpecialObject F T Δ) :=
  (Classical.choose_spec
    (Classification.segmentSpecialConstituentExistence.{uF, max uF uV} F T Δ)).1

theorem segmentSocleObject_hasFiniteLength (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    (segmentSocleObject F T Δ).HasFiniteLength := by
  let := T.topology
  obtain ⟨_, _, h⟩ := segmentSocleObject_spec F T Δ
  exact SmoothRep.hasFiniteLength_of_isIrreducible h.1

theorem segmentSpecialObject_hasFiniteLength (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    (segmentSpecialObject F T Δ).HasFiniteLength := by
  let := T.topology
  obtain ⟨_, _, h⟩ := segmentSpecialObject_spec F T Δ
  exact SmoothRep.hasFiniteLength_of_isIrreducible h.1

/-- Any supplied strong socle is actually isomorphic to the chosen object.
This is stronger than equality of virtual classes. -/
theorem segmentSocleObject_iso (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSocle Δ π → Nonempty (segmentSocleObject F T Δ ≅ π) := by
  let := T.topology
  intro π hπ
  obtain ⟨A, hA, h⟩ := segmentSocleObject_spec F T Δ
  have h' := (T.isSegmentSocle_iff Δ π A hA).mp hπ
  obtain ⟨e⟩ := h.nonempty_socleEquiv
  obtain ⟨e'⟩ := h'.nonempty_socleEquiv
  exact ⟨SmoothRep.mkIso (e.trans e'.symm)⟩

/-- Any supplied strong special head is actually isomorphic to the chosen object. -/
theorem segmentSpecialObject_iso (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentHead Δ π → Nonempty (segmentSpecialObject F T Δ ≅ π) := by
  let := T.topology
  intro π hπ
  obtain ⟨A, hA, h⟩ := segmentSpecialObject_spec F T Δ
  have h' := (T.isSegmentHead_iff Δ π A hA).mp hπ
  obtain ⟨e⟩ := h.nonempty_headEquiv
  obtain ⟨e'⟩ := h'.nonempty_headEquiv
  exact ⟨SmoothRep.mkIso (e.symm.trans e')⟩

/-- Exact K0 class of the actual segment socle. -/
def segmentSocleClass (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} Δ.degree F.Carrier :=
  letI := T.topology
  GeneralLinear.finiteLengthClass Δ.degree F.Carrier
    (segmentSocleObject F T Δ) (segmentSocleObject_hasFiniteLength F T Δ)

/-- Exact K0 class of the actual special quotient. -/
def segmentSpecialClass (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} Δ.degree F.Carrier :=
  letI := T.topology
  GeneralLinear.finiteLengthClass Δ.degree F.Carrier
    (segmentSpecialObject F T Δ) (segmentSpecialObject_hasFiniteLength F T Δ)

/-- Transport from a supplied actual segment socle to its canonical class. -/
theorem segmentSocleClass_of_object (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
      (hπ : π.HasFiniteLength), T.IsSegmentSocle Δ π →
      segmentSocleClass F T Δ = GeneralLinear.finiteLengthClass Δ.degree F.Carrier π hπ := by
  let := T.topology
  intro π hπ hs
  obtain ⟨e⟩ := segmentSocleObject_iso F T Δ π hs
  exact SmoothRep.FiniteLengthGrothendieckGroup.ofObject_eq_of_iso e

theorem segmentSpecialClass_of_object (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
      (hπ : π.HasFiniteLength), T.IsSegmentHead Δ π →
      segmentSpecialClass F T Δ = GeneralLinear.finiteLengthClass Δ.degree F.Carrier π hπ := by
  let := T.topology
  intro π hπ hs
  obtain ⟨e⟩ := segmentSpecialObject_iso F T Δ π hs
  exact SmoothRep.FiniteLengthGrothendieckGroup.ofObject_eq_of_iso e

/-- The segment generator in the actual graded group. -/
def gradedSegmentSocle (Δ : T.Segment.{max uF uV, uF}) :
    GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  gradedInclusion F T Δ.degree (segmentSocleClass F T Δ)

/-- The special quotient class in the actual graded group. -/
def gradedSegmentSpecial (Δ : T.Segment.{max uF uV, uF}) :
    GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  gradedInclusion F T Δ.degree (segmentSpecialClass F T Δ)

/-- Reuse of the existing unadjusted segment exchange, with the exact
support-dependent sign. It is an identity of virtual classes. -/
theorem alternatingOperator_segmentSocleClass (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    alternatingOperator F T Δ.degree (segmentSocleClass F T Δ) =
      (-1 : ℤ) ^ (Δ.degree - Δ.length) • segmentSpecialClass F T Δ := by
  let := T.topology
  exact segmentSocleHead F T Δ (segmentSocleObject F T Δ) (segmentSpecialObject F T Δ)
    (segmentSocleObject_spec F T Δ) (segmentSpecialObject_spec F T Δ)

end Langlands.Aubert
