import Langlands.Representation.Aubert.AdjustedMultisegmentExchangeStatement
import Langlands.Representation.Aubert.HeadProductLeadingTerm

/-!
# Actual adjusted Aubert exchange for a multisegment

The support-adjusted Aubert operator sends the exact class of a weak
Zelevinsky subrepresentation to that of a weak Langlands quotient with the
same multisegment. The proof combines two published results: every weak
Langlands quotient is the adjusted image of a socle label of its multisegment,
and socle labels of a multisegment are unique.
-/

noncomputable section

namespace Langlands.Aubert

open SegmentPolynomialSurjectivity

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- **Actual adjusted Aubert exchange on weak multisegment labels.** In every
rank, the support-adjusted Aubert operator sends the exact finite-length class
of a weak Zelevinsky subrepresentation to the exact finite-length class of a
weak Langlands quotient with the same multisegment. -/
theorem adjustedMultisegmentExchange :
    AdjustedMultisegmentExchangeStatement.{uF, uV} F T := by
  let := T.topology
  intro n dZ dL Z L hZ hL hmult
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  have hx := binaryProductExactness.{uF, uV} F T
  have hl := gradedInductionRingLaws F T hx
  obtain ⟨c, hc, he⟩ :=
    HeadProductLeadingTerm.exists_socleLabel_of_isLanglandsQuotient F T dL L hL
  have hZc : IsLabel F T dL.multisegment n
      (GeneralLinear.irreducibleIsoClass n F.Carrier Z hZ.2.2.1) :=
    ⟨Z, hZ.2.2.1, rfl, dZ, hmult, hZ⟩
  rw [LanglandsHeadDuality.isLabel_unique F T hx hl ψ hc hZc,
    basisClass_irreducibleIsoClass, basisClass_irreducibleIsoClass,
    gradedAdjustedOperator_homogeneous] at he
  have he' := congrArg (fun x : GradedGrothendieckGroup.{uF, uV} F T => x n) he
  simpa only [gradedInclusion_apply_self] using he'

end Langlands.Aubert
