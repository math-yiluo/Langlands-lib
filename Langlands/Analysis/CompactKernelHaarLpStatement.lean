import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Haar and Lp comparison along open homomorphisms with compact kernel

Internal analytic targets for comparing actual central quotient measures.
-/

namespace Langlands

open MeasureTheory

universe uG uH uE

/-- A continuous open surjective homomorphism with compact kernel is proper. -/
def CompactKernelProperMapStatement : Prop :=
  ∀ (G : Type uG) (H : Type uH)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H]
    (q : G →ₜ* H),
    Function.Surjective q → IsOpenMap q →
    IsCompact (q.ker : Set G) → IsProperMap q

/-- Actual Haar pushforward, positive scalar comparison, and continuous-function
`MemLp` comparison for an open surjective homomorphism with compact kernel. -/
def CompactKernelHaarLpMeasureStatement : Prop :=
  ∀ (G : Type uG) (H : Type uH)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    (q : G →ₜ* H),
    Function.Surjective q → IsOpenMap q → IsCompact (q.ker : Set G) →
    ∀ (μ : Measure G) (ν : Measure H)
      [Measure.IsHaarMeasure μ] [Measure.IsHaarMeasure ν],
      Measure.IsHaarMeasure (Measure.map q μ) ∧
      (∃ C : ℝ, 0 < C ∧ Measure.map q μ = ENNReal.ofReal C • ν) ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] (f : H → E) (p : ENNReal),
        Continuous f → (MemLp (f ∘ q) p μ ↔ MemLp f p ν)

/-- The topology and measure comparison obligations, with independent group,
quotient and function-value universes. -/
def CompactKernelHaarLpComparisonStatement : Prop :=
  CompactKernelProperMapStatement.{uG, uH} ∧
    CompactKernelHaarLpMeasureStatement.{uG, uH, uE}

end Langlands
