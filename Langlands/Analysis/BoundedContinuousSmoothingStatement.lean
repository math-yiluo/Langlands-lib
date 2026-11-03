import Langlands.Analysis.OperatorIdeals
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Algebra.Algebra.NonUnitalHom

noncomputable section

open MeasureTheory
open scoped MeasureTheory BoundedContinuousFunction

namespace Langlands.Analysis.OperatorIdeals

universe u v w

/-- A bounded-continuous lift of an operator in an isometrically realized
Hilbert space gives a Hilbert–Schmidt operator. -/
def HilbertSchmidtBoundedContinuousLiftStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X : Type v) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (j : E →ₗᵢ[ℂ] Lp ℂ 2 μ) (A : E →L[ℂ] E)
    (S : E →L[ℂ] (X →ᵇ ℂ)),
    (∀ z, j (A z) = BoundedContinuousFunction.toLp 2 μ ℂ (S z)) →
    IsHilbertSchmidt A

/-- Smoothing for every test-algebra element and finite product factorization
imply trace class for every operator in a nonunital representation. -/
def TraceClassFiniteFactorizationSmoothingStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X : Type v) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (T : Type w) [NonUnitalRing T] [Module ℂ T]
    [IsScalarTower ℂ T T] [SMulCommClass ℂ T T]
    (j : E →ₗᵢ[ℂ] Lp ℂ 2 μ) (R : T →ₙₐ[ℂ] (E →L[ℂ] E)),
    (∀ f : T, ∃ S : E →L[ℂ] (X →ᵇ ℂ),
      ∀ z, j (R f z) = BoundedContinuousFunction.toLp 2 μ ℂ (S z)) →
    (∀ f : T, ∃ (n : ℕ) (a b : Fin n → T), f = ∑ i, a i * b i) →
    ∀ f : T, IsTraceClass (R f)

/-- The single-operator lift criterion and the all-test-function trace-class
criterion for a finitely product-generated nonunital test algebra. -/
def BoundedContinuousSmoothingCriteriaStatement : Prop :=
  HilbertSchmidtBoundedContinuousLiftStatement.{u, v} ∧
    TraceClassFiniteFactorizationSmoothingStatement.{u, v, w}

end Langlands.Analysis.OperatorIdeals
