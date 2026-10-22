import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.EvaluationDefinitions
import Langlands.Geometry.Analytic.Affinoid

/-! # Weighted evaluation and the bounded universal property target -/

universe u v w

namespace Langlands.Analytic.GeneralizedTateAlgebra

/-- Convergent weighted evaluation with its explicit norm estimate, necessity
of the monomial bound, and uniqueness from coordinate images. Completeness is
required only of the target in the existence clauses. -/
def BoundedUniversalPropertyStatement : Prop :=
  (∀ (σ : Type u) (r : PositivePolyradius σ)
    (K : Type v) [NormedField K] [IsUltrametricDist K]
    (B : Type w) [NormedCommRing B] [NormedAlgebra K B]
    [IsUltrametricDist B] [CompleteSpace B] (b : σ → B),
    HasBoundedMonomials r B b →
      (∀ f : GeneralizedTateAlgebra r K,
        HasSum (evaluationTerm r K B b f) (evaluate r K B b f)) ∧
      (∀ C : ℝ, 0 < C →
        (∀ d : σ →₀ ℕ, ‖StrictTateAlgebra.monomialValue σ B b d‖ ≤ C * r.weight d) →
        ∀ f : GeneralizedTateAlgebra r K, ‖evaluate r K B b f‖ ≤ C * ‖f‖) ∧
      ∃ φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B,
        (∀ f, φ f = evaluate r K B b f) ∧ ∀ i, φ (X r K i) = b i) ∧
  (∀ (σ : Type u) (r : PositivePolyradius σ)
    (K : Type v) [NormedField K] [IsUltrametricDist K]
    (B : Type w) [NormedCommRing B] [NormedAlgebra K B],
    (∀ φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B,
      HasBoundedMonomials r B (fun i => φ (X r K i))) ∧
    (∀ φ ψ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B,
      (∀ i, φ (X r K i) = ψ (X r K i)) → φ = ψ)) ∧
  (∀ (σ : Type u) (r : PositivePolyradius σ)
    (K : Type v) [NormedField K] [IsUltrametricDist K]
    (B : Type w) [NormedCommRing B] [NormedAlgebra K B]
    [IsUltrametricDist B] [CompleteSpace B] (b : σ → B),
    HasBoundedMonomials r B b ↔
      ∃! φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B,
        ∀ i, φ (X r K i) = b i)

end Langlands.Analytic.GeneralizedTateAlgebra
