import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Exact coefficient extraction for normalized Jacquet exponents

A generalized exponent of an admissible representation is realized by one
smooth matrix coefficient on a sufficiently deep full block-scalar chamber.
-/

namespace Langlands

universe uF uV

/-- Every generalized normalized upper Jacquet exponent is exactly a smooth
matrix coefficient divided by the positive half modulus throughout a sufficiently
deep block-scalar chamber, with unrestricted common scalar multiplication. -/
def GLJacquetExponentCoefficientExtractionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      letI := T.topology
      IsAdmissible ρ →
      ∀ (B : GeneralLinear.BlockShape n)
        (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
        T.IsJacquetExponent B ρ χ →
        ∃ (v : V) (ℓ : SmoothDual ρ) (ε : ℝ), 0 < ε ∧ ε ≤ 1 ∧
          ∀ a : Fin B.length → F.Carrierˣ,
            (∀ i j : Fin B.length, i < j →
              T.normalizedAbs ((a i : F.Carrier) / (a j : F.Carrier)) < ε) →
            ℓ.1 (ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) v) =
              (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) * (χ a : ℂ)

end Langlands
