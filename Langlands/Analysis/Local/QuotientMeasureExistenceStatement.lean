import Langlands.Analysis.Local.QuotientMeasure

/-!
# Compatible quotient-measure existence under the full group hypotheses
-/

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure

universe u

/-- Compatible measure existence for a closed subgroup, with the complete
locally compact Hausdorff and regular two-sided Haar hypotheses. -/
def CompatibleMeasureExistsForClosedSubgroups : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G), IsClosed (H : Set G) →
    ∀ [MeasurableSpace H] [BorelSpace H]
      (μG : Measure G) (μH : Measure H)
      [IsHaarMeasure μG] [μG.Regular] [IsMulRightInvariant μG]
      [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
      [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)],
      CompatibleMeasureExists H μG μH

end Langlands.QuotientIntegration
