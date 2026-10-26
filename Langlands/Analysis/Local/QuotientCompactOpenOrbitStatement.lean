import Langlands.Analysis.Local.QuotientTopology

/-!
# Restricting a compatible quotient measure to a compact open orbit

The normalization is inherited from the actual ambient Haar restriction to K.
This file states an internal consequence of the compact-test Weil formula.
-/

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure

universe uG

/-- On the orbit of `H g` under a compact open subgroup `K`, a compatible
quotient measure is the pushforward of the actual Haar restriction to `K`,
divided by the subgroup mass of `H ∩ g K g⁻¹`. -/
def CompactOpenOrbitMeasureStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G), IsClosed (H : Set G) →
    ∀ [MeasurableSpace H] [BorelSpace H]
      [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
      (μG : Measure G) (μH : Measure H)
      [IsHaarMeasure μG] [μG.Regular]
      [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
      (K : OpenSubgroup G), IsCompact (K : Set G) →
      ∀ (μ : Measure (LeftQuotient H)), IsCompatible H μG μH μ →
      ∀ g : G,
        let q := leftQuotientMap H
        let Cg := (fun k : G => q (g * k)) '' (K : Set G)
        let Sg := {h : H | g⁻¹ * (h : G) * g ∈ K}
        let c := μH Sg
        let κ := μG.restrict (K : Set G)
        0 < c ∧ c < ⊤ ∧
          μ.restrict Cg = c⁻¹ • Measure.map (fun k : G => q (g * k)) κ

end Langlands.QuotientIntegration
