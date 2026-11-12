import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Etale.Basic

/-! # Finite-order etale specialization of a smooth algebra -/

universe u

namespace Langlands.CommutativeAlgebra

/-- A map from a smooth algebra to the completion of a Noetherian local ring
can be approximated to any finite order through an etale algebra. -/
def SmoothEtaleCompletionApproximationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Type u) [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (f : B →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R) (N : ℕ),
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Algebra.Etale R E ∧
        ∃ (g : B →ₐ[R] E)
          (ι : E →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R),
          (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) N).comp (ι.comp g) =
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) N).comp f

end Langlands.CommutativeAlgebra
