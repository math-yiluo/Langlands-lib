import Langlands.Representation.Aubert.HeadProductLeadingTermStatement
import Langlands.Representation.Aubert.GradedGrothendieck
import Langlands.Representation.Classification.MultisegmentHeadExistenceProof
import Langlands.Representation.Classification.MultisegmentHeadExhaustionProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadClassificationProof
import Langlands.Representation.Classification.SegmentSocleInversionReduction
import Langlands.Representation.Smooth.IrreducibleClassDetection

/-! # Internal assembly for neighboring Speh product irreducibility -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Classification.SpehNeighborProduct

open PadicField.TopologicalData SmoothRep VirtualRepresentation
open SmoothRep.IrreducibleGrothendieckProof Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Published head exhaustion supplies a weak head datum for every actual
irreducible constituent, without a positive-rank premise. -/
theorem exists_weakHead {n : ℕ} :
    letI := T.topology
    ∀ (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      C.IsIrreducible →
      ∃ dC : T.SegmentProductDatum.{max uF uV, uF} n, dC.IsLanglandsQuotient C := by
  let := T.topology
  intro C hC
  obtain ⟨_, _, dC, _, hdC⟩ := multisegmentHeadExhaustion.{uF, uV} F T n C hC
  exact ⟨dC, hdC.isLanglandsQuotient⟩

/-- Published head existence supplies, at the matching rank, a weak head datum
and an actual head for every multisegment. -/
theorem exists_head {a : T.Multisegment.{max uF uV, uF}} {m : ℕ} (hm : a.degree = m) :
    letI := T.topology
    ∃ (d : T.SegmentProductDatum.{max uF uV, uF} m)
      (L : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      d.multisegment = a ∧ d.IsLanglandsQuotient L := by
  let := T.topology
  subst m
  obtain ⟨L, d, hd, hL⟩ := multisegmentHeadExistence.{uF, uV} F T a
  exact ⟨d, L, hd, hL.isLanglandsQuotient⟩

/-- If every constituent head label is the sum of the two input head labels,
leading multiplicity one detects actual irreducibility of the product. -/
theorem isIrreducible_of_constituent_multisegment_eq
    (hH : HeadProductLeadingTermStatement.{uF, uV} F T) {m n : ℕ}
    (dA : T.SegmentProductDatum.{max uF uV, uF} m)
    (dB : T.SegmentProductDatum.{max uF uV, uF} n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      dA.IsLanglandsQuotient A → dB.IsLanglandsQuotient B →
      (∀ (dC : T.SegmentProductDatum.{max uF uV, uF} (m + n))
        (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier)),
        dC.IsLanglandsQuotient C →
        IsSubquotient C ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)) →
        dC.multisegment = dA.multisegment + dB.multisegment) →
      ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)).IsIrreducible := by
  classical
  let := T.topology
  intro A B hA hB hlabels
  let P := (T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)
  have hfin : P.HasFiniteLength := binaryProduct_preservesFiniteLength F T m n A B
    (hasFiniteLength_of_isIrreducible hA.2.2.1) (hasFiniteLength_of_isIrreducible hB.2.2.1)
  have hdegree : (dA.multisegment + dB.multisegment).degree = m + n := by
    calc
      _ = dA.multisegment.degree + dB.multisegment.degree := by
        simp only [Multisegment.degree, Multiset.map_add, Multiset.sum_add]
      _ = m + n := congrArg₂ (· + ·) dA.multisegment_degree dB.multisegment_degree
  obtain ⟨dH, H, hdH, hH'⟩ := exists_head F T hdegree
  have hmult := (hH m n dA dB dH A B H hA hB hH').2.1 hdH hfin
  let cH := GeneralLinear.irreducibleIsoClass (m + n) F.Carrier H hH'.2.2.1
  apply isIrreducible_of_compositionFactors_eq_generator ⟨P, hfin⟩ cH
  ext c
  by_cases hc : c = cH
  · subst c
    rw [compositionFactors_apply _ H hH'.2.2.1, hmult]
    simp [generator, cH]
  · obtain ⟨C, hC, rfl⟩ := IrreducibleIsoClass.exists_eq c
    have hzero : compositionMultiplicity ⟨P, hfin⟩ C = 0 := by
      by_contra hne
      have hsub : IsSubquotient C P :=
        (compositionMultiplicity_pos_iff_isSubquotient ⟨P, hfin⟩ C hC).mp
          (Nat.pos_of_ne_zero hne)
      obtain ⟨dC, hdC⟩ := exists_weakHead F T C hC
      have he := hlabels dC C hdC hsub
      have hiso : Nonempty (C ≅ H) :=
        (orderedMultisegmentHeadClassification.{uF, uV} F T (m + n)
          dC dH C H hdC hH').mp (he.trans hdH.symm)
      exact hc ((SmoothRep.irreducibleIsoClass_eq_iff _ _).mpr hiso)
    rw [compositionFactors_apply _ C hC, hzero]
    simp [generator, Ne.symm hc]

/-- For a uniform-length input label, a bound of that length on every
constituent label suffices for actual product irreducibility. -/
theorem isIrreducible_of_constituent_segment_length_le
    (hH : HeadProductLeadingTermStatement.{uF, uV} F T) {m n l : ℕ}
    (dA : T.SegmentProductDatum.{max uF uV, uF} m)
    (dB : T.SegmentProductDatum.{max uF uV, uF} n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      dA.IsLanglandsQuotient A → dB.IsLanglandsQuotient B →
      (∀ Δ ∈ dA.multisegment + dB.multisegment, Δ.length = l) →
      (∀ (dC : T.SegmentProductDatum.{max uF uV, uF} (m + n))
        (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier)),
        dC.IsLanglandsQuotient C →
        IsSubquotient C ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)) →
        ∀ Δ ∈ dC.multisegment, Δ.length ≤ l) →
      ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)).IsIrreducible := by
  let := T.topology
  intro A B hA hB hlen hbound
  apply isIrreducible_of_constituent_multisegment_eq F T hH dA dB A B hA hB
  intro dC C hC hsub
  by_contra hne
  obtain ⟨Δ, hΔ, hlt⟩ := (hH m n dA dB dC A B C hA hB hC).2.2 l hsub hlen hne
  exact absurd (hbound dC C hC hsub Δ hΔ) (Nat.not_le.mpr hlt)

end Langlands.Classification.SpehNeighborProduct
