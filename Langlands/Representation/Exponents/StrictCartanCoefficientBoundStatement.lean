import Langlands.Group.GL.CartanQuotientDefinitions
import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Strict exponential decay of smooth coefficients in the normalized Cartan chamber

This proposition specifies a coefficient bound for an arbitrary admissible
representation with a unitary scalar character and strict normalized Jacquet
exponent bounds. It does not prove the estimate or square-integrability.
-/

namespace Langlands

universe uF uV

/-- Strict normalized Jacquet bounds imply a polynomial times strict exponential
bound, multiplied by the positive half modulus, uniformly over both actual
maximal compact factors for each fixed smooth coefficient. -/
def GLStrictCartanCoefficientBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (ω : F.Carrierˣ →* ℂˣ),
      letI := T.topology
      IsAdmissible ρ →
      (∀ (a : F.Carrierˣ) (v : V),
        ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v) →
      (∀ a : F.Carrierˣ, ‖(ω a : ℂ)‖ = 1) →
      (∀ (B : GeneralLinear.BlockShape n)
        (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
        T.IsJacquetExponent B ρ χ →
        ∀ a : Fin B.length → F.Carrierˣ,
          Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
          (∃ i j, T.normalizedAbs (a i : F.Carrier) ≠
            T.normalizedAbs (a j : F.Carrier)) →
          ‖(χ a : ℂ)‖ < 1) →
      ∀ (v : V) (ℓ : SmoothDual ρ),
        ∃ (C : ℝ) (d : ℕ) (r : ℝ), 0 < C ∧ 0 < r ∧ r < 1 ∧
          ∀ lam : Fin n → ℤ, GeneralLinear.CartanQuotient.Normalized lam →
            ∀ k₁ ∈ GeneralLinear.CartanQuotient.maximalCompact T n,
              ∀ k₂ ∈ GeneralLinear.CartanQuotient.maximalCompact T n,
                ‖ℓ.1 (ρ (k₁ * GeneralLinear.CartanQuotient.representative T lam * k₂) v)‖ ≤
                  C * Real.sqrt (GeneralLinear.CartanQuotient.delta T lam) *
                    (GeneralLinear.CartanQuotient.height lam) ^ d *
                    Real.rpow r (GeneralLinear.CartanQuotient.height lam - 1)

end Langlands
