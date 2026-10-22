import Langlands.Geometry.Analytic.TateSeries.Definitions

/-! # Coefficientwise Tate evaluation data and actual monomial bounds -/

noncomputable section

universe u v w

namespace Langlands.Analytic.StrictTateAlgebra

variable (σ : Type u) (K : Type v) (B : Type w)
  [NormedField K] [IsUltrametricDist K]
  [NormedCommRing B] [NormedAlgebra K B]

/-- Evaluate a monomial exponent at a family of algebra elements. -/
def monomialValue (b : σ → B) (d : σ →₀ ℕ) : B :=
  d.prod fun i n => b i ^ n

/-- A tuple is bounded for Tate evaluation if all its finite monomials share
a positive norm bound. This condition refers to actual products in the algebra. -/
def HasBoundedMonomials (b : σ → B) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : σ →₀ ℕ, ‖monomialValue σ B b d‖ ≤ C

/-- The evaluated coefficient monomial of a Tate series. -/
def evaluationTerm (b : σ → B) (f : StrictTateAlgebra σ K) (d : σ →₀ ℕ) : B :=
  algebraMap K B (MvPowerSeries.coeff d (series σ K f)) * monomialValue σ B b d

/-- Evaluation is the actual sum of the evaluated coefficient monomials.
The following theorems prove convergence for tuples with bounded monomials. -/
def evaluate (b : σ → B) (f : StrictTateAlgebra σ K) : B :=
  ∑' d, evaluationTerm σ K B b f d

end Langlands.Analytic.StrictTateAlgebra
