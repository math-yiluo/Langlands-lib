import Langlands.Representation.GodementJacquet.AnalyticData

/-!
# Representation-equivalence transport of normalized matrix equation data

This internal statement retains the full published data predicate on both
actual representations, with independent universes for their carriers.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis

universe uF uV uW

/-- Equivalent representations have exactly the same normalized matrix
functional-equation data, with every scalar and measure fixed. -/
def NormalizedMatrixFunctionalEquationTransportStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F]
    [MeasurableSpace F] (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (_e : σ.Equiv τ) (P PDual : Polynomial ℂ) (c : ℂˣ) (m : ℤ),
    NormalizedMatrixFunctionalEquationData q ψ ν abv μ σ P PDual c m ↔
      NormalizedMatrixFunctionalEquationData q ψ ν abv μ τ P PDual c m

end Langlands.GodementJacquet
