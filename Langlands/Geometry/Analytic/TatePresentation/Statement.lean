import Langlands.Geometry.Analytic.TatePresentation.Definitions

/-! # Bounded universal property of actual Tate relation quotients -/

universe u v

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

open StrictTateAlgebra

/-- The actual quotient by the closure of the relation ideal admits bounded
evaluation, coordinate uniqueness, and precisely the bounded solutions. -/
def RelationsUniversalPropertyStatement : Prop :=
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K]
    (n : ℕ) (relations : Set (StrictTateAlgebra (Fin n) K))
    (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
    [IsUltrametricDist B] [CompleteSpace B] (b : Fin n → B),
    HasBoundedMonomials (Fin n) B b →
    (∀ f ∈ relations, evaluate (Fin n) K B b f = 0) →
      ∃ φ : BoundedAlgHom K (ofRelations K n relations) B,
        (∀ f, φ (presentationMap K (ofRelations K n relations) f) =
          evaluate (Fin n) K B b f) ∧
        ∀ i, φ (coordinate K (ofRelations K n relations) i) = b i) ∧
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n : ℕ) (relations : Set (StrictTateAlgebra (Fin n) K))
    (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
    (φ ψ : BoundedAlgHom K (ofRelations K n relations) B),
    (∀ i, φ (coordinate K (ofRelations K n relations) i) =
      ψ (coordinate K (ofRelations K n relations) i)) → φ = ψ) ∧
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n : ℕ) (relations : Set (StrictTateAlgebra (Fin n) K))
    (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
    [IsUltrametricDist B] [CompleteSpace B] (b : Fin n → B),
    (∃! φ : BoundedAlgHom K (ofRelations K n relations) B,
      ∀ i, φ (coordinate K (ofRelations K n relations) i) = b i) ↔
      HasBoundedMonomials (Fin n) B b ∧
        ∀ f ∈ relations, evaluate (Fin n) K B b f = 0)

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
