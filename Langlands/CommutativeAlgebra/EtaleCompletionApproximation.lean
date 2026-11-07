import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Etale.Basic

/-! # Approximation of finite systems in an etale neighbourhood -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Finite-type algebra maps to the completion of a local ring can be
approximated to any finite order through an etale algebra over that ring.
The comparison is equality after the canonical projection to `P / 𝔪^N`. -/
def EtaleCompletionApproximation (P : Type u) [CommRing P] [IsLocalRing P] : Prop :=
  ∀ (C : Type u) [CommRing C] [Algebra P C] [Algebra.FiniteType P C]
    (f : C →ₐ[P] AdicCompletion (IsLocalRing.maximalIdeal P) P) (N : ℕ),
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra P E),
      Algebra.Etale P E ∧
        ∃ (g : C →ₐ[P] E)
          (ι : E →ₐ[P] AdicCompletion (IsLocalRing.maximalIdeal P) P),
          (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal P) N).comp (ι.comp g) =
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal P) N).comp f

end Langlands.CommutativeAlgebra
