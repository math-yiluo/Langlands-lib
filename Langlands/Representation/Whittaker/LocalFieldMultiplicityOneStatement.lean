import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Smooth.Definitions
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Whittaker multiplicity at most one over every nonarchimedean local field

Bernstein–Zelevinsky 1976, Theorem 5.16 (Gelfand–Kazhdan), in the scalar form of
`MultiplicityOneStatement`, for every nonarchimedean local field, including positive
characteristic. This module defines an unproved proposition.
-/

namespace Langlands.Whittaker

universe uF uV

/-- Bernstein–Zelevinsky 1976, Theorem 5.16. For every nonarchimedean local field `F`
(any characteristic), every rank `n + 1`, every nontrivial unitary additive character
`ψ` and every irreducible admissible complex representation `π` of `GL_(n+1)(F)`, every
standard `ψ`-Whittaker functional is a unique complex multiple of any specified nonzero
one. -/
def LocalFieldMultiplicityOneStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
    IsAdmissible π → Representation.IsIrreducible π →
    ∀ ℓ₁ ℓ₂ : glFunctionals ψ n π, ℓ₁.val ≠ 0 →
      ∃! c : ℂ, ℓ₂ = c • ℓ₁

end Langlands.Whittaker
