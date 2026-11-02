import Langlands.Representation.Plancherel.CentralSubgroupCoefficients
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Comparison of the actual split-central and full-central quotients

These internal targets retain compactness of the actual central fiber.
-/

namespace Langlands.Plancherel

open MeasureTheory

universe uG uV

/-- The actual central projection is an open surjection with compact kernel,
and hence proper, when the quotient of the center by the subgroup is compact. -/
def CentralQuotientCompactKernelStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G),
    IsClosed (A : Set G) →
    ∀ [CompactSpace (Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G))],
      Function.Surjective (centralQuotientProjection A hA) ∧
      IsOpenMap (centralQuotientProjection A hA) ∧
      IsCompact ((centralQuotientProjection A hA).ker : Set (G ⧸ A)) ∧
      IsProperMap (centralQuotientProjection A hA)

/-- Comparison of actual coefficient `MemLp` conditions and the published
square-integrability predicates on the two central quotients. -/
def CentralSubgroupCoefficientLpComparisonStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G),
    IsClosed (A : Set G) →
    ∀ [CompactSpace (Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G))]
      [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
      [MeasurableSpace (G ⧸ Subgroup.center G)]
      [BorelSpace (G ⧸ Subgroup.center G)]
      (μA : Measure (G ⧸ A)) (μZ : Measure (G ⧸ Subgroup.center G))
      [Measure.IsHaarMeasure μA] [Measure.IsHaarMeasure μZ]
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V),
      (∀ (c : UnitaryCentralCharacter ρ) (ℓ : Module.Dual ℂ V)
        (v : V) (p : ENNReal), IsSmoothVector ρ v →
        (MemLp (centralSubgroupCoefficientNorm A hA c ℓ v) p μA ↔
          MemLp (c.coefficientNorm ℓ v) p μZ)) ∧
      (IsSquareIntegrableModCentralSubgroup A hA ρ μA ↔
        IsSquareIntegrableModCenter ρ μZ)

/-- Topology and analytic comparison for an actual closed central subgroup
with compact quotient in the center. -/
def CentralSubgroupSquareIntegrabilityComparisonStatement : Prop :=
  CentralQuotientCompactKernelStatement.{uG} ∧
    CentralSubgroupCoefficientLpComparisonStatement.{uG, uV}

end Langlands.Plancherel
