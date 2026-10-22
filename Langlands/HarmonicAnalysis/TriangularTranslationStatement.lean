import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure

/-!
# Finite triangular translations of product measures

An internal measure-theoretic prerequisite for Haar measure in upper block
unipotent coordinates. This file states the prerequisite and does not prove it.
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory

universe uI uX

/-- A measurable translation in each coordinate, depending only on coordinates
of strictly lower rank, preserves a finite product of translation-invariant
sigma-finite measures. -/
def FiniteTriangularTranslationStatement : Prop :=
  ∀ (ι : Type uI) [Fintype ι] (X : ι → Type uX)
    [∀ i, AddCommGroup (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableAdd₂ (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsAddLeftInvariant]
    (rank : ι → ℕ) (f : (∀ i, X i) → ∀ i, X i),
    Measurable f →
    (∀ (i : ι) (x y : ∀ j, X j),
      (∀ j, rank j < rank i → x j = y j) → f x i = f y i) →
    MeasurePreserving (fun x i => f x i + x i) (Measure.pi μ) (Measure.pi μ)

end Langlands.HarmonicAnalysis
