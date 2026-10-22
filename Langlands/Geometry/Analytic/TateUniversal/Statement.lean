import Langlands.Geometry.Analytic.TateUniversal.Definitions

/-! # Exact target for bounded evaluation and the strict Tate universal property -/

universe u v w

namespace Langlands.Analytic.StrictTateAlgebra

/-- Actual convergent evaluation, finite monomial bounds, and the bounded
universal property, with completeness only where each assertion needs it. -/
def BoundedUniversalPropertyStatement : Prop :=
  (∀ (σ : Type u) (B : Type w) [NormedCommRing B] [Fintype σ] (b : σ → B),
    HasBoundedMonomials σ B b ↔
      ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖b i ^ n‖ ≤ C) ∧
  (∀ (σ : Type u) (K : Type v) [NormedField K] [IsUltrametricDist K]
    (B : Type w) [NormedCommRing B] [NormedAlgebra K B]
    [IsUltrametricDist B] [CompleteSpace B] (b : σ → B),
    HasBoundedMonomials σ B b →
      (∀ f : StrictTateAlgebra σ K,
        HasSum (evaluationTerm σ K B b f) (evaluate σ K B b f)) ∧
      ∃ φ : BoundedAlgHom K (StrictTateAlgebra σ K) B,
        (∀ f, φ f = evaluate σ K B b f) ∧ ∀ i, φ (X σ K i) = b i) ∧
  (∀ (σ : Type u) (K : Type v) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (B : Type w) [NormedCommRing B] [NormedAlgebra K B],
    (∀ φ : BoundedAlgHom K (StrictTateAlgebra σ K) B,
      HasBoundedMonomials σ B (fun i => φ (X σ K i))) ∧
    (∀ φ ψ : BoundedAlgHom K (StrictTateAlgebra σ K) B,
      (∀ i, φ (X σ K i) = ψ (X σ K i)) → φ = ψ)) ∧
  (∀ (σ : Type u) (K : Type v) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (B : Type w) [NormedCommRing B] [NormedAlgebra K B]
    [IsUltrametricDist B] [CompleteSpace B] (b : σ → B),
    HasBoundedMonomials σ B b →
      ∃! φ : BoundedAlgHom K (StrictTateAlgebra σ K) B,
        ∀ i, φ (X σ K i) = b i)

end Langlands.Analytic.StrictTateAlgebra
