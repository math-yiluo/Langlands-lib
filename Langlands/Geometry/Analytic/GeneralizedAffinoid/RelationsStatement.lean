import Langlands.Geometry.Analytic.GeneralizedAffinoid.Relations
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.EvaluationDefinitions

/-! # Coordinate solutions for finite weighted relation quotients: target -/

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

/-- Bounded coordinate solutions are represented by the actual weighted
relation quotient, with each supplied positive monomial bound retained.
No clause assumes coefficient completeness. -/
def RelationsUniversalPropertyStatement : Prop :=
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K]
    (n : ℕ) (r : PositivePolyradius (Fin n))
    (relations : Set (GeneralizedTateAlgebra r K))
    (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
    [IsUltrametricDist B] [CompleteSpace B] (b : Fin n → B),
    HasBoundedMonomials r B b →
    (∀ f ∈ relations, evaluate r K B b f = 0) →
      ∃ φ : BoundedAlgHom K (ofRelations K n r relations) B,
        (∀ f, φ (presentationMap K (ofRelations K n r relations) f) =
          evaluate r K B b f) ∧
        (∀ i, φ (coordinate K (ofRelations K n r relations) i) = b i) ∧
        (∀ C : ℝ, 0 < C →
          (∀ d : Fin n →₀ ℕ,
            ‖StrictTateAlgebra.monomialValue (Fin n) B b d‖ ≤ C * r.weight d) →
          ∀ a : ofRelations K n r relations, ‖φ a‖ ≤ C * ‖a‖)) ∧
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K]
    (n : ℕ) (r : PositivePolyradius (Fin n))
    (relations : Set (GeneralizedTateAlgebra r K))
    (B : Type v) [NormedCommRing B] [NormedAlgebra K B],
    (∀ φ : BoundedAlgHom K (ofRelations K n r relations) B,
      HasBoundedMonomials r B
        (fun i => φ (coordinate K (ofRelations K n r relations) i))) ∧
    (∀ φ ψ : BoundedAlgHom K (ofRelations K n r relations) B,
      (∀ i, φ (coordinate K (ofRelations K n r relations) i) =
        ψ (coordinate K (ofRelations K n r relations) i)) → φ = ψ)) ∧
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K]
    (n : ℕ) (r : PositivePolyradius (Fin n))
    (relations : Set (GeneralizedTateAlgebra r K))
    (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
    [IsUltrametricDist B] [CompleteSpace B] (b : Fin n → B),
    (HasBoundedMonomials r B b ∧
      ∀ f ∈ relations, evaluate r K B b f = 0) ↔
      ∃! φ : BoundedAlgHom K (ofRelations K n r relations) B,
        ∀ i, φ (coordinate K (ofRelations K n r relations) i) = b i)

end Langlands.Analytic.PresentedAffinoidAlgebra
