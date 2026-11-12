import Langlands.Representation.Aubert.SupportSign
import Langlands.Representation.Classification.LanglandsData

/-!
# Actual adjusted Aubert exchange for a multisegment

An internal proposition target relating the existing weak Zelevinsky and
Langlands label relations through the actual support-adjusted operator.
-/

noncomputable section

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual adjusted Aubert operator sends the exact class of a weak
Zelevinsky subrepresentation to that of a weak Langlands quotient with the
same multisegment. Both finite-length witnesses come from irreducibility. -/
def AdjustedMultisegmentExchangeStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (dZ dL : T.SegmentProductDatum.{max uF uV, uF} n)
    (Z L : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hZ : dZ.IsZelevinskySubrepresentation Z) (hL : dL.IsLanglandsQuotient L),
    dZ.multisegment = dL.multisegment →
      adjustedOperator.{uF, uV} F T n
        (GeneralLinear.finiteLengthClass n F.Carrier Z
          (SmoothRep.hasFiniteLength_of_isIrreducible hZ.2.2.1)) =
      GeneralLinear.finiteLengthClass n F.Carrier L
        (SmoothRep.hasFiniteLength_of_isIrreducible hL.2.2.1)

end Langlands.Aubert
