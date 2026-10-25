import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Finite products in `MemLp`

These closed propositions state preservation under separated finite products
and reflection when no factor is almost everywhere equal to zero.
No proofs are supplied here.
-/

open scoped BigOperators

namespace Langlands

universe uι uX

/-- A separated product of real `L^r` functions belongs to `L^r` for the actual
finite product measure, with no nonzero hypotheses on its factors. -/
def FiniteProductMemLpPreservationStatement : Prop :=
  ∀ (ι : Type uι) [Fintype ι] [Nonempty ι]
    (X : ι → Type uX) [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, MeasureTheory.SigmaFinite (μ i)]
    (f : ∀ i, X i → ℝ) (r : ℝ),
    0 < r →
    (∀ i, MeasureTheory.MemLp (f i) (ENNReal.ofReal r) (μ i)) →
    MeasureTheory.MemLp (fun x : (i : ι) → X i => ∏ i, f i (x i))
      (ENNReal.ofReal r) (MeasureTheory.Measure.pi μ)

/-- For a.e. strongly measurable real factors, each not a.e. zero, membership
of the separated product in `L^r` is equivalent to membership of every factor.
Reflection assumes no factor integrability in advance. -/
def FiniteProductMemLpNonzeroIffStatement : Prop :=
  ∀ (ι : Type uι) [Fintype ι] [Nonempty ι]
    (X : ι → Type uX) [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, MeasureTheory.SigmaFinite (μ i)]
    (f : ∀ i, X i → ℝ),
    (∀ i, MeasureTheory.AEStronglyMeasurable (f i) (μ i)) →
    (∀ i, ¬ (f i =ᵐ[μ i] (0 : X i → ℝ))) →
    ∀ (r : ℝ), 0 < r →
      (MeasureTheory.MemLp (fun x : (i : ι) → X i => ∏ i, f i (x i))
        (ENNReal.ofReal r) (MeasureTheory.Measure.pi μ) ↔
        ∀ i, MeasureTheory.MemLp (f i) (ENNReal.ofReal r) (μ i))

/-- Preservation and nonzero-factor reflection for separated finite products,
for every positive finite real exponent. -/
def FiniteProductMemLpStatement : Prop :=
  FiniteProductMemLpPreservationStatement.{uι, uX} ∧
    FiniteProductMemLpNonzeroIffStatement.{uι, uX}

end Langlands
