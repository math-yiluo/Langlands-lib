import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # Scalar meromorphic identity with a finite sum in changed coordinates -/

universe u v

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

/-- If a scalar meromorphic function agrees on a nonempty open patch with a
finite sum of products of meromorphic coefficients and meromorphic functions
pulled back by a linear equivalence, the equality holds on the common
holomorphy domain. The conclusion also covers an empty sum. -/
def ScalarMeromorphicSumIdentityStatement : Prop :=
  ∀ (X : Type u) [AddCommGroup X] [Module ℂ X]
    (Y : Type v) [AddCommGroup Y] [Module ℂ Y] (e : X ≃ₗ[ℂ] Y)
    (f : X → ℂ) (U V : Set X) (W : Set Y) (k : ℕ)
    (coeff : Fin k → X → ℂ) (g : Fin k → Y → ℂ),
    IsMeromorphicInCoordinatesOn f U →
    (∀ i, IsMeromorphicInCoordinatesOn (coeff i) V) →
    (∀ i, IsMeromorphicInCoordinatesOn (g i) W) →
    ∀ (n : ℕ) (c : (Fin n → ℂ) ≃ₗ[ℂ] X) (O : Set (Fin n → ℂ)),
      IsOpen O → O.Nonempty →
      (∀ x ∈ O, f (c x) = ∑ i, coeff i (c x) * g i (e (c x))) →
      ∀ x ∈ U ∩ V, e x ∈ W → f x = ∑ i, coeff i x * g i (e x)

end Langlands.Analysis.Meromorphic
