import Langlands.AbelianScheme.PolarizedFiniteLevel.Data

/-! # Doubles of divisors of actual polarizations are polarizations -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Let `A` be an actual abelian scheme with chosen dual witnesses and let `mu` be an
actual map to the constructed dual. If `k • mu` is a polarization for some positive integer
`k`, then `2 • mu` is a polarization. This proposition is a statement target, not a proof. -/
def PolarizationDoublingDivisionStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (S : Scheme.{u}) (A : AbelianScheme S) (W : DualWitness A)
    (mu : A ⟶ W.dual P) (k : ℕ), 0 < k →
      W.IsPolarization P (k • mu) → W.IsPolarization P (2 • mu)

end Langlands.AbelianScheme.PolarizedFiniteLevel
