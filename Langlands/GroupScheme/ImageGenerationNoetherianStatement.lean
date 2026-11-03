import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finiteness targets for schematic product generation -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.ImageGeneration

/-- Prime-ideal chains stabilize in the direction required by increasing
integral schematic product images. -/
def NoetherianPrimeChainStabilizationStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (p : ℕ → Ideal A), Antitone p → (∀ n, (p n).IsPrime) →
      ∃ N, ∀ m, N ≤ m → p m = p N

/-- A closed self-embedding of a Noetherian affine scheme is invertible. -/
def NoetherianAffineClosedEndomorphismStatement : Prop :=
  ∀ (X : Scheme.{u}) [IsAffine X] [IsLocallyNoetherian X]
    (φ : X ⟶ X), IsClosedImmersion φ → IsIso φ

/-- The two finiteness inputs used in product-image stabilization and
closed-submonoid inversion. -/
def NoetherianImageGenerationFinitenessStatement : Prop :=
  NoetherianPrimeChainStabilizationStatement.{u} ∧
    NoetherianAffineClosedEndomorphismStatement.{u}

end Langlands.GroupScheme.ImageGeneration
