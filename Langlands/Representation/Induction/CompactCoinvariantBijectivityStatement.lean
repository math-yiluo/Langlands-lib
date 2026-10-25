import Langlands.Representation.Induction.CompactCoinvariantIntegral
import Langlands.Analysis.Local.QuotientMeasure

/-! Bijectivity target for the actual compact-induction quotient integral. -/

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure

universe uG uV

/-- The supplied compatible quotient integral is bijective on ambient
coinvariants for every smooth inducing representation. This is a statement,
with independent group and coefficient universes, not a proof. -/
def CompactCoinvariantIntegralBijective : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G],
    (∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ (H : Subgroup G), IsClosed (H : Set G) →
    ∀ [MeasurableSpace H] [BorelSpace H]
      (μG : Measure G) (μH : Measure H)
      [IsHaarMeasure μG] [μG.Regular] [IsMulRightInvariant μG]
      [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
      [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
      [BorelSpace (QuotientIntegration.LeftQuotient H)]
      (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
      (hν : QuotientIntegration.IsCompatible H μG μH ν)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ H V),
      IsSmooth σ →
        Function.Bijective (compactCoinvariantDesc H σ ν hν.right_invariant)

end Langlands.Induction
