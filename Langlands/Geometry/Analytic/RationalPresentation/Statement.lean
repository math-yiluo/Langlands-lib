import Langlands.Geometry.Analytic.RationalPresentation.Definitions

/-! # Bounded extension target for rational presentations -/

universe u v

namespace Langlands.Analytic.RationalPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

/-- The algebraic unit-ideal condition controls denominators and gives uniqueness;
explicit bounded solutions give existence of extensions from the rational quotient. -/
def BoundedExtensionStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
    (g : StrictTateAlgebra (Fin n) K) (f : Fin m → StrictTateAlgebra (Fin n) K),
    (GeneratesUnitIdeal K n m S g f →
      IsUnit (baseMap K n m S g f (presentationMap K (ofRelations K n S) g))) ∧
    (GeneratesUnitIdeal K n m S g f →
      ∀ x : BanachSpectrum (ofRelations K n S), x ∈ locus K n m S g f →
        x (presentationMap K (ofRelations K n S) g) ≠ 0) ∧
    (∀ x : BanachSpectrum (algebra K n m S g f),
      BanachSpectrum.comap (baseMap K n m S g f).toBoundedRingHom x ∈
        locus K n m S g f) ∧
    (∀ (B : Type v) [NormedCommRing B] [NormedAlgebra K B],
      GeneratesUnitIdeal K n m S g f →
      ∀ φ ψ : BoundedAlgHom K (algebra K n m S g f) B,
        φ.comp (baseMap K n m S g f) = ψ.comp (baseMap K n m S g f) → φ = ψ) ∧
    (∀ (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
      [IsUltrametricDist B] [CompleteSpace B],
      GeneratesUnitIdeal K n m S g f →
      ∀ (φ : BoundedAlgHom K (ofRelations K n S) B) (b : Fin m → B),
        HasBoundedMonomials (Fin m) B b →
        (∀ j, φ (presentationMap K (ofRelations K n S) g) * b j =
          φ (presentationMap K (ofRelations K n S) (f j))) →
        ∃! ψ : BoundedAlgHom K (algebra K n m S g f) B,
          ψ.comp (baseMap K n m S g f) = φ)

end Langlands.Analytic.RationalPresentation
