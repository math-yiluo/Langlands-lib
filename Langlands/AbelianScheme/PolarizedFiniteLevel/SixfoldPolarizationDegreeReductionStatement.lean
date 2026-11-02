import Langlands.AbelianScheme.PolarizedFiniteLevel.Data

/-! # Conditional native degree of the sixfold polarization -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- The native degree of `6 • polarization`, conditional on the finite flat
degree of the actual multiplication-by-six endomorphism. -/
def SixfoldPolarizationDegreeReductionStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] (g d n : ℕ)
    (a : Datum P (Spec (CommRingCat.of K)) g d n),
    IsFinite (hom ((6 : ℕ) • 𝟙 a.abelian)) →
    Flat (hom ((6 : ℕ) • 𝟙 a.abelian)) →
    HasConstantDegree (hom ((6 : ℕ) • 𝟙 a.abelian)) (6 ^ (2 * g)) →
    IsFinite (hom (6 • a.polarization)) ∧
      Flat (hom (6 • a.polarization)) ∧
      HasConstantDegree (hom (6 • a.polarization)) (6 ^ (2 * g) * d ^ 2)

end Langlands.AbelianScheme.PolarizedFiniteLevel
