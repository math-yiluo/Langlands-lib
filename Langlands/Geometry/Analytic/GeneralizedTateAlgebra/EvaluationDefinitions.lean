import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Definitions
import Langlands.Geometry.Analytic.TateEvaluation.Definitions

/-! # Actual weighted monomial bounds and series evaluation formulas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.GeneralizedTateAlgebra

variable {σ : Type u} (r : PositivePolyradius σ)

/-- A tuple has a uniform bound relative to the weights of all its actual
finite monomials. The constant includes the empty monomial. -/
def HasBoundedMonomials (B : Type w) [NormedCommRing B] (b : σ → B) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : σ →₀ ℕ,
    ‖StrictTateAlgebra.monomialValue σ B b d‖ ≤ C * r.weight d

@[simp] theorem hasBoundedMonomials_unit (B : Type w) [NormedCommRing B] (b : σ → B) :
    HasBoundedMonomials (PositivePolyradius.unit σ) B b ↔
      StrictTateAlgebra.HasBoundedMonomials σ B b := by
  simp only [HasBoundedMonomials, PositivePolyradius.unit_weight, mul_one,
    StrictTateAlgebra.HasBoundedMonomials]

variable (K : Type v) [NormedCommRing K] [IsUltrametricDist K]

/-- The actual coordinate series at the specified polyradius. -/
def X (i : σ) : GeneralizedTateAlgebra r K :=
  monomial r K (Finsupp.single i 1) 1

theorem norm_X (i : σ) : ‖X r K i‖ = ‖(1 : K)‖ * r i := by
  simp [X, norm_monomial, PositivePolyradius.weight]

@[simp] theorem norm_X_of_normOne [NormOneClass K] (i : σ) : ‖X r K i‖ = r i := by
  rw [norm_X, norm_one, one_mul]

section Evaluation

variable (B : Type w) [NormedCommRing B] [Algebra K B]

/-- The actual coefficient monomial evaluated in the target algebra. -/
def evaluationTerm (b : σ → B) (f : GeneralizedTateAlgebra r K) (d : σ →₀ ℕ) : B :=
  algebraMap K B (MvPowerSeries.coeff d (series r K f)) *
    StrictTateAlgebra.monomialValue σ B b d

/-- The actual sum of the evaluated coefficient monomials. Convergence and
algebra-map laws require separate proofs; this formula assumes neither. -/
def evaluate (b : σ → B) (f : GeneralizedTateAlgebra r K) : B :=
  ∑' d, evaluationTerm r K B b f d

end Evaluation

section UnitComparison

variable {K : Type v} [NormedField K] [IsUltrametricDist K]
  (B : Type w) [NormedCommRing B] [NormedAlgebra K B]

@[simp] theorem evaluationTerm_unit (b : σ → B)
    (f : GeneralizedTateAlgebra (PositivePolyradius.unit σ) K) (d : σ →₀ ℕ) :
    evaluationTerm (PositivePolyradius.unit σ) K B b f d =
      StrictTateAlgebra.evaluationTerm σ K B b (unitAlgEquiv K f) d := rfl

@[simp] theorem evaluate_unit (b : σ → B)
    (f : GeneralizedTateAlgebra (PositivePolyradius.unit σ) K) :
    evaluate (PositivePolyradius.unit σ) K B b f =
      StrictTateAlgebra.evaluate σ K B b (unitAlgEquiv K f) := rfl

end UnitComparison

end Langlands.Analytic.GeneralizedTateAlgebra
