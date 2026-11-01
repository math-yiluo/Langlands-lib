import Langlands.Representation.GodementJacquet.AnalyticData

/-!
# Descent of normalized matrix equation data through coefficient inclusion

The target coefficient family has its own normalized generators. Membership of
one in both target Laurent spans is an explicit premise of this internal helper.
-/

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV uW

/-- Full matrix equation data descend through an inclusion of actual coefficient
spaces when both target value modules contain one. The normalized polynomials,
complex unit and integer exponent may change. -/
def NormalizedMatrixFunctionalEquationDescentStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
    [TotallyDisconnectedSpace F] (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    1 < q → IsSelfDual ψ ν →
    biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients σ →
    (1 : RationalFunctions) ∈ zetaSpan (matrixRationalValues q abv μ τ) →
    (1 : RationalFunctions) ∈ zetaSpan (iotaMatrixRationalValues q abv μ τ) →
    ∀ (P PDual : Polynomial ℂ) (c : ℂˣ) (m : ℤ),
      NormalizedMatrixFunctionalEquationData q ψ ν abv μ σ P PDual c m →
      ∃ (Q QDual : Polynomial ℂ) (d : ℂˣ) (a : ℤ),
        NormalizedMatrixFunctionalEquationData q ψ ν abv μ τ Q QDual d a

end Langlands.GodementJacquet
