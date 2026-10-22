import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Exponents.Jacquet

/-!
# Casselman's exponent criterion for square-integrability on `GL_n`

Square-integrability modulo the center is compared with strict bounds on the
exponents of every normalized standard Jacquet module, evaluated on the
non-compact part of the closed negative block-scalar chamber.
-/

namespace Langlands

universe uF uV

/-- Casselman's exponent criterion for square-integrability modulo the center,
for a nonzero admissible representation of `GL_n(F)` on which the scalar
matrices act through a character `ω`. -/
def GLSquareIntegrableExponentCriterionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (ω : F.Carrierˣ →* ℂˣ),
      (letI := T.topology
       IsAdmissible ρ) →
      (∀ (a : F.Carrierˣ) (v : V), ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v) →
      (T.IsSquareIntegrable ρ ↔
        (∀ a : F.Carrierˣ, ‖(ω a : ℂ)‖ = 1) ∧
        ∀ (B : GeneralLinear.BlockShape n) (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
          T.IsJacquetExponent B ρ χ →
          ∀ a : Fin B.length → F.Carrierˣ,
            Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
            (∃ i j, T.normalizedAbs (a i : F.Carrier) ≠
              T.normalizedAbs (a j : F.Carrier)) →
            ‖(χ a : ℂ)‖ < 1)

end Langlands
