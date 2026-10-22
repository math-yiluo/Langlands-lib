import Langlands.Representation.Hecke.NormalizedIndicator

/-! # Compact-open local units for finite families in the actual Hecke algebra -/

universe u

namespace Langlands.Hecke.HeckeAlgebra

/-- Every finite family has a normalized compact-open two-sided local unit,
with its subgroup contained in any prescribed open subgroup. -/
def FiniteFamilyLocalUnitsStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure],
    ∀ (s : Finset (HeckeAlgebra μ)) (U : OpenSubgroup G),
      ∃ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
        K ≤ U ∧
        normalizedIndicator μ K hK * normalizedIndicator μ K hK =
          normalizedIndicator μ K hK ∧
        ∀ f ∈ s, normalizedIndicator μ K hK * f = f ∧
          f * normalizedIndicator μ K hK = f

end Langlands.Hecke.HeckeAlgebra
