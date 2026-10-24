import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Countable-cell tests for finite positive Lp exponents -/

namespace Langlands

open MeasureTheory
open scoped ENNReal NNReal

/-- A summable upper bound on a countable cover gives finite positive Lp
integrability. The covering sets need not be measurable or disjoint. -/
def CountableCellLpUpperStatement.{uX, uI} : Prop :=
  ∀ (X : Type uX) [MeasurableSpace X] (I : Type uI) [Countable I]
    (μ : Measure X) (f : X → ℝ) (p : ℝ≥0∞),
    p ≠ 0 → p ≠ ∞ → AEStronglyMeasurable f μ →
    ∀ (s : I → Set X), (⋃ i, s i) = Set.univ →
    ∀ (b : I → ℝ≥0∞),
      (∀ i x, x ∈ s i → ‖f x‖ₑ ≤ b i) →
      (∑' i, (b i) ^ p.toReal * μ (s i)) < ∞ →
      MemLp f p μ

/-- Lp integrability forces the weighted lower bounds on disjoint measurable
cells to have finite sum; the cells need not cover the space. -/
def CountableCellLpLowerStatement.{uX, uI} : Prop :=
  ∀ (X : Type uX) [MeasurableSpace X] (I : Type uI) [Countable I]
    (μ : Measure X) (f : X → ℝ) (p : ℝ≥0∞),
    p ≠ 0 → p ≠ ∞ → MemLp f p μ →
    ∀ (s : I → Set X), (∀ i, MeasurableSet (s i)) →
      Pairwise (fun i j => Disjoint (s i) (s j)) →
    ∀ (b : I → ℝ≥0∞),
      (∀ i x, x ∈ s i → b i ≤ ‖f x‖ₑ) →
      (∑' i, (b i) ^ p.toReal * μ (s i)) < ∞

/-- Elementary measure-theoretic upper and lower tests for later coefficient
estimates on actual Cartan cells. -/
def CountableCellLpStatement.{uX, uI} : Prop :=
  CountableCellLpUpperStatement.{uX, uI} ∧
    CountableCellLpLowerStatement.{uX, uI}

end Langlands
