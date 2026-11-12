import Langlands.Representation.Aubert.ZelevinskyComparison

/-!
# Support-adjusted Aubert exchange on actual segment classes

The signed segment formula determines the support sign by effectivity.
The two signs then cancel in exact K0 and in its graded direct sum.
-/

noncomputable section

namespace Langlands.Aubert

open SmoothRep VirtualRepresentation
open SmoothRep.IrreducibleGrothendieckProof SmoothRep.IrreducibleOperator

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The effective-sign characterization computes the support sign of the
actual segment socle from the published signed segment exchange. -/
theorem supportSign_segmentSocleObject (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    ∀ hπ : (segmentSocleObject F T Δ).IsIrreducible,
      supportSign.{uF, uV} F T Δ.degree
        (irreducibleIsoClass (segmentSocleObject F T Δ) hπ) =
          (-1 : ℤ) ^ (Δ.degree - Δ.length) := by
  let := T.topology
  intro hπ
  apply supportSign_eq_of_effective F T _ _ _ (neg_one_pow_eq_or ℤ _)
  simp only [onIrreducibles, LinearMap.comp_apply,
    realizeIrreducibles_generator_irreducibleIsoClass
      (segmentSocleObject F T Δ) hπ (hasFiniteLength_of_isIrreducible hπ)]
  change (-1 : ℤ) ^ (Δ.degree - Δ.length) •
    factorMap (alternatingOperator F T Δ.degree (segmentSocleClass F T Δ)) ∈ effective
  rw [alternatingOperator_segmentSocleClass, map_zsmul, smul_smul, ← mul_pow]
  simp only [neg_mul_neg, one_mul, one_pow, one_smul]
  rw [segmentSpecialClass, GeneralLinear.finiteLengthClass, factorMap_ofRepresentation]
  exact compositionFactors_effective _

/-- The support-adjusted operator exchanges actual homogeneous segment classes
with no sign. -/
theorem adjustedOperator_segmentSocleClass (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    adjustedOperator.{uF, uV} F T Δ.degree (segmentSocleClass F T Δ) =
      segmentSpecialClass F T Δ := by
  let := T.topology
  obtain ⟨_, _, hπ⟩ := segmentSocleObject_spec F T Δ
  rw [segmentSocleClass, adjustedOperator_irreducible F T Δ.degree _ hπ.1,
    supportSign_segmentSocleObject]
  change (-1 : ℤ) ^ (Δ.degree - Δ.length) •
    alternatingOperator F T Δ.degree (segmentSocleClass F T Δ) = _
  rw [alternatingOperator_segmentSocleClass, smul_smul, ← mul_pow]
  simp

/-- The whole published adjusted segment-exchange proposition, with independent
field and representation universes and no additional hypotheses. -/
theorem adjustedSegmentExchange : AdjustedSegmentExchangeStatement.{uF, uV} F T := by
  let := T.topology
  intro Δ
  change gradedOperator F T (adjustedOperator F T)
    (gradedInclusion F T Δ.degree (segmentSocleClass F T Δ)) =
      gradedInclusion F T Δ.degree (segmentSpecialClass F T Δ)
  rw [gradedOperator_homogeneous, adjustedOperator_segmentSocleClass]

end Langlands.Aubert
