import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalPresentation
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.EvaluationDefinitions

/-! # Bounded extension target for weighted rational presentations -/

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

open GeneralizedTateAlgebra

/-- Denominator control and bounded extensions from the actual weighted rational
quotient. Coordinate-specified extensions do not require unit-ideal generation;
uniqueness from the base alone does. No clause assumes coefficient completeness. -/
def BoundedExtensionStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K]
    (A : PresentedAffinoidAlgebra K) (m : ℕ) (s : PositivePolyradius (Fin m))
    (g : GeneralizedTateAlgebra A.polyradius K)
    (f : Fin m → GeneralizedTateAlgebra A.polyradius K),
    (GeneratesUnitIdeal K A g f →
      IsUnit (baseMap K A s g f (presentationMap K A g))) ∧
    (GeneratesUnitIdeal K A g f →
      ∀ x : BanachSpectrum A, x ∈ locus K A s g f →
        x (presentationMap K A g) ≠ 0) ∧
    (∀ (B : Type v) [NormedCommRing B] [NormedAlgebra K B],
      GeneratesUnitIdeal K A g f →
      ∀ φ ψ : BoundedAlgHom K (algebra K A s g f) B,
        φ.comp (baseMap K A s g f) = ψ.comp (baseMap K A s g f) → φ = ψ) ∧
    (∀ (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
      [IsUltrametricDist B] [CompleteSpace B],
      ∀ (φ : BoundedAlgHom K A B) (b : Fin m → B),
        HasBoundedMonomials s B b →
        (∀ j, φ (presentationMap K A g) * b j = φ (presentationMap K A (f j))) →
        ∃! ψ : BoundedAlgHom K (algebra K A s g f) B,
          ψ.comp (baseMap K A s g f) = φ ∧
            ∀ j, ψ (fraction K A s g f j) = b j) ∧
    (∀ (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
      [IsUltrametricDist B] [CompleteSpace B],
      GeneratesUnitIdeal K A g f →
      ∀ (φ : BoundedAlgHom K A B) (b : Fin m → B),
        HasBoundedMonomials s B b →
        (∀ j, φ (presentationMap K A g) * b j = φ (presentationMap K A (f j))) →
        ∃! ψ : BoundedAlgHom K (algebra K A s g f) B,
          ψ.comp (baseMap K A s g f) = φ)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
