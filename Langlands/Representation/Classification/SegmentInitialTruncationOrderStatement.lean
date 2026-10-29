import Langlands.Representation.Classification.SegmentInitialTruncation
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement

/-! # Nonprecedence after one-step initial truncation -/

namespace Langlands.Classification

universe uF uV

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- On a free integral twist line, initial truncation creates no new precedence
between surviving terms and preserves every supplied nonprecedence list order. -/
def SegmentInitialTruncationOrder : Prop :=
  CuspidalIntegralTwistFreeness.{uF, uV} F T →
    (∀ Δ Γ Δ' Γ' : Segment.{uV, uF} T,
      Δ.dropLast = some Δ' →
      Γ.dropLast = some Γ' →
      Δ'.Precedes Γ' → Δ.Precedes Γ) ∧
    (∀ l : List (Segment.{uV, uF} T),
      T.IsPrecedenceOrderedList l →
      T.IsPrecedenceOrderedList (Segment.dropLastList l))

end Langlands.Classification
