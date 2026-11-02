import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Classification.SegmentTruncationObstructionStatement

/-!
# Support bound for derivatives of supplied special heads

This module states a support-only bound for an independent proof successor.
It proves neither this bound nor a derivative formula or irreducibility theorem.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every actual simple subquotient of every derivative of a
supplied special head has an actual supercuspidal support whose underlying set
is an optional terminal truncation of the original segment. -/
def SegmentHeadDerivativeSupportTruncation : Prop :=
  letI := T.topology
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (Δ : T.Segment.{uV, uF})
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    T.IsSegmentHead Δ π →
    ∀ (k : ℕ) (hk : k ≤ Δ.degree)
      (σ : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (Δ.degree - k) F.Carrier)),
      σ.IsIrreducible →
      SmoothRep.IsSubquotient σ ((Derivative.generalLinearDerivative T ψ Δ.degree k hk).obj π) →
      ∃ (s : Multiset (T.CuspidalDatum.{uV, uF}))
        (A : Option (T.Segment.{uV, uF})),
        T.IsSupercuspidalSupport σ s ∧
        PadicField.TopologicalData.Segment.IsTerminalTruncation A Δ ∧
        {ρ | ρ ∈ s} = PadicField.TopologicalData.Segment.optionalSupport A

end Langlands.Classification
