import Langlands.Group.GL.CartanQuotientDefinitions
import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Polynomial Cartan coefficient bound from weak normalized Jacquet exponent bounds

This proposition specifies a coefficient bound for an arbitrary admissible
representation with a scalar central character and weak normalized Jacquet
exponent bounds. It does not prove the estimate, temperedness, or any
integrability statement.
-/

namespace Langlands

universe uF uV

/-- Weak normalized Jacquet bounds imply that each fixed smooth coefficient is
bounded on the normalized Cartan chamber by a constant times the positive half
modulus times a polynomial in the height, uniformly over both actual maximal
compact factors. -/
def GLCartanCoefficientBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (ω : F.Carrierˣ →* ℂˣ),
      letI := T.topology
      IsAdmissible ρ →
      (∀ (a : F.Carrierˣ) (v : V),
        ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v) →
      (∀ (B : GeneralLinear.BlockShape n)
        (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
        T.IsJacquetExponent B ρ χ →
        ∀ a : Fin B.length → F.Carrierˣ,
          Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
          ‖(χ a : ℂ)‖ ≤ 1) →
      ∀ (v : V) (ℓ : SmoothDual ρ),
        ∃ (C : ℝ) (d : ℕ), 0 < C ∧
          ∀ lam : Fin n → ℤ, GeneralLinear.CartanQuotient.Normalized lam →
            ∀ k₁ ∈ GeneralLinear.CartanQuotient.maximalCompact T n,
              ∀ k₂ ∈ GeneralLinear.CartanQuotient.maximalCompact T n,
                ‖ℓ.1 (ρ (k₁ * GeneralLinear.CartanQuotient.representative T lam * k₂) v)‖ ≤
                  C * Real.sqrt (GeneralLinear.CartanQuotient.delta T lam) *
                    (GeneralLinear.CartanQuotient.height lam) ^ d

end Langlands
