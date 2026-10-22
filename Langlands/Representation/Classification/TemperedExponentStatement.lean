import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Exponents.Jacquet

/-!
# The exponent criterion for temperedness on `GL_n`

Temperedness modulo the center is compared with weak bounds on the exponents of
every normalized standard Jacquet module, evaluated on the closed negative
block-scalar chamber.
-/

namespace Langlands

universe uF uV

/-- The exponent criterion for temperedness, for an admissible representation of
`GL_n(F)` on which the scalar matrices act through a character `ω`. -/
def GLTemperedExponentCriterionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (ω : F.Carrierˣ →* ℂˣ),
      (letI := T.topology
       IsAdmissible ρ) →
      (∀ (a : F.Carrierˣ) (v : V), ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v) →
      (T.IsTempered ρ ↔
        ∀ (B : GeneralLinear.BlockShape n) (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
          T.IsJacquetExponent B ρ χ →
          ∀ a : Fin B.length → F.Carrierˣ,
            Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
            ‖(χ a : ℂ)‖ ≤ 1)

end Langlands
