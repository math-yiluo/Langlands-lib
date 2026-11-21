import Langlands.AbelianScheme.PolarizedFiniteLevel.Data

/-! # Positivity of integral proportionality between actual polarizations -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Let `A` be an actual abelian scheme of positive relative dimension over a nonempty
base, with chosen dual witnesses. If two actual polarizations `lam` and `lam'` of `A`
satisfy `a • lam' = b • lam` for integers `a ≠ 0` and `b`, then `a * b > 0`. Thus two
polarizations on the same rational ray have a positive ratio. This proposition is a
statement target, not a proof. -/
def PolarizationRayPositivityStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (S : Scheme.{u}) (_ : Nonempty S) (A : AbelianScheme S) (g : ℕ),
    0 < g → A.HasRelativeDimension g →
    ∀ (W : DualWitness A) (lam lam' : A ⟶ W.dual P),
      W.IsPolarization P lam → W.IsPolarization P lam' →
      ∀ (a b : ℤ), a ≠ 0 → a • lam' = b • lam → 0 < a * b

end Langlands.AbelianScheme.PolarizedFiniteLevel
