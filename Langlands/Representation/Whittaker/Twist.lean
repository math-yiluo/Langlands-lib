import Langlands.Representation.Whittaker.AlgebraicTwist
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# Determinant twists of GL Whittaker coefficient models

The actual upper-unipotent determinant is one, so the algebraic coefficient-model
construction specializes to every determinant character and positive rank.
-/

noncomputable section

namespace Langlands.Whittaker

universe uF uV

section GeneralLinear

open GeneralLinear HarmonicAnalysis

variable {F : Type uF} [CommRing F] [TopologicalSpace F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace F] in
/-- The determinant character is trivial on the actual upper-unipotent group. -/
theorem determinantCharacter_unipotent (χ : Fˣ →* ℂˣ)
    (u : upperUnipotent (n + 1) F) :
    (χ.comp determinant) u.val = 1 := by
  have hdet : determinant u.val = 1 := by
    apply Units.ext
    change Matrix.det u.val.val = 1
    rw [Matrix.det_of_isUpperTriangular u.property.1]
    simp only [UpperUnipotent.entry_diag, Finset.prod_const_one]
  change χ (determinant u.val) = 1
  rw [hdet, map_one]

/-- The determinant twist preserves the actual standard-character functional space. -/
def determinantTwistFunctionalEquiv (ψ : UnitaryAdditiveCharacter F)
    (χ : Fˣ →* ℂˣ) (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    glFunctionals ψ n π ≃ₗ[ℂ] glFunctionals ψ n (Langlands.twist (χ.comp determinant) π) :=
  twistFunctionalEquiv _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π

/-- Specialization of the coefficient-model equivalence to actual GL determinant twists. -/
def determinantTwistModelEquiv (ψ : UnitaryAdditiveCharacter F)
    (χ : Fˣ →* ℂˣ) (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n π) :
    (Langlands.twist (χ.comp determinant)
      (V := (coefficientModel π ℓ).toSubmodule) (modelRepresentation π ℓ)).Equiv
        (modelRepresentation (Langlands.twist (χ.comp determinant) π)
          (determinantTwistFunctionalEquiv ψ χ π ℓ)) :=
  twistModelEquiv _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π ℓ

/-- An open kernel in the field units gives an open kernel after determinant pullback. -/
theorem determinantCharacter_openKernel [IsTopologicalRing F] (χ : Fˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set Fˣ)) :
    IsOpen ((χ.comp (determinant (n := n + 1))).ker :
      Set (Langlands.GeneralLinear (n + 1) F)) :=
  hχ.preimage (determinantContinuous (n := n + 1) (R := F)).continuous

/-- Smoothness of the actual determinant-twisted coefficient model. -/
theorem determinantTwistModel_isSmooth [IsTopologicalRing F]
    (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set Fˣ))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) (hπ : IsSmooth π)
    (ℓ : glFunctionals ψ n π) :
    IsSmooth
      (V := (coefficientModel (Langlands.twist (χ.comp determinant) π)
        (determinantTwistFunctionalEquiv ψ χ π ℓ)).toSubmodule)
      (modelRepresentation (Langlands.twist (χ.comp determinant) π)
        (determinantTwistFunctionalEquiv ψ χ π ℓ)) :=
  twistModel_isSmooth _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π
    (determinantCharacter_openKernel χ hχ) hπ ℓ

end GeneralLinear

end Langlands.Whittaker
