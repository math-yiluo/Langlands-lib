import Langlands.Geometry.Analytic.WeierstrassPresentation.Definitions

/-! # Bounded extension target for actual Weierstrass quotients -/

universe u v

namespace Langlands.Analytic.WeierstrassPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

/-- Forward spectrum inclusion, uniqueness on the base, and existence of bounded
extensions when the constrained elements have bounded powers. -/
def BoundedExtensionStatement : Prop :=
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
    (f : Fin m → StrictTateAlgebra (Fin n) K)
    (x : BanachSpectrum (algebra K n m S f)),
    BanachSpectrum.comap (baseMap K n m S f).toBoundedRingHom x ∈ locus K n m S f) ∧
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
    (f : Fin m → StrictTateAlgebra (Fin n) K)
    (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
    (φ ψ : BoundedAlgHom K (algebra K n m S f) B),
    φ.comp (baseMap K n m S f) = ψ.comp (baseMap K n m S f) → φ = ψ) ∧
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
    (f : Fin m → StrictTateAlgebra (Fin n) K)
    (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
    [IsUltrametricDist B] [CompleteSpace B]
    (φ : BoundedAlgHom K (ofRelations K n S) B),
    (∀ j, ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, ‖φ (presentationMap K (ofRelations K n S) (f j)) ^ r‖ ≤ C) →
    ∃! ψ : BoundedAlgHom K (algebra K n m S f) B,
      ψ.comp (baseMap K n m S f) = φ)

end Langlands.Analytic.WeierstrassPresentation
