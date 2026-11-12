import Langlands.Representation.Aubert.AdjustedHomogeneousMultiplicativityProof
import Langlands.Representation.Aubert.AdjustedSegmentExchangeProof
import Langlands.Representation.Aubert.AdjustedInvolutivityProof

/-!
# Aubert 1995 Theorem 2.3 for the support-adjusted GL Aubert operator

The published homogeneous multiplicativity extends to the whole graded ring.
With unit preservation and the adjusted segment exchange, the polynomial
universal property identifies the resulting ring endomorphism with the
constructed Zelevinsky endomorphism. Involutivity of the additive adjusted
operator then transfers to that endomorphism.
-/

noncomputable section

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)
  (hp : SegmentPolynomialComparisonStatement F T hx hl)

/-- Aubert 1995 Theorem 2.3 for the actual support-adjusted operator on the
whole graded GL Grothendieck ring, with Zelevinsky's §9.12 involutivity. -/
theorem aubertTheorem23 : AubertTheorem23Statement.{uF, uV} F T hx hl hp := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have hm : AdjustedMultiplicativityStatement F T hx :=
    gradedOperator_multiplicative_of_homogeneous F T (adjustedOperator F T) hx
      (adjustedHomogeneousMultiplicativity F T hx)
  have hc := gradedOperatorRingHom_eq_zelevinsky F T (adjustedOperator F T) hx hl hp hm
    (gradedAdjustedOperator_unit F T) (adjustedSegmentExchange F T)
  have hy : ∀ y, gradedAdjustedOperator F T y = zelevinskyEndomorphism F T hx hl hp y :=
    fun y => RingHom.congr_fun hc y
  refine ⟨hm, ?_, LinearMap.ext hy⟩
  intro x
  rw [← hy, ← hy]
  exact adjustedInvolutivity F T x

end Langlands.Aubert
