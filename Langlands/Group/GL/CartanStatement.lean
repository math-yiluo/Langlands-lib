import Langlands.Representation.Whittaker.Iwasawa

/-!
# Cartan decomposition over a discretely valued field

The exponent tuple is unique; the two integral factors need not be unique.
-/

namespace Langlands.GeneralLinear

universe uF uΓ

/-- Every invertible matrix has a unique decreasing tuple of integer elementary
exponents in an integral–diagonal–integral factorization. -/
def CartanDecompositionStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (Γ₀ : Type uΓ) [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (ϖ : Fˣ),
    Iwasawa.IsUniformizingElement v ϖ →
      ∀ (m : ℕ) (g : Matrix.GeneralLinearGroup (Fin m) F),
        ∃! lam : Fin m → ℤ, Antitone lam ∧
          ∃ k₁ ∈ Iwasawa.integralRange v m,
            ∃ k₂ ∈ Iwasawa.integralRange v m,
              g = k₁ * Iwasawa.torus ϖ lam * k₂

end Langlands.GeneralLinear
