import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof

/-! # Scalar generalized characters and the ambient centre in Jacquet modules -/

namespace Langlands

universe uG uC uF uV

/-- Scalar action detects every generalized eigencharacter. The second clause
also supplies occurrence when the carrier is nontrivial. -/
def ScalarGeneralizedEigencharacterDetection : Prop :=
  (∀ (G : Type uG) [Group G] (C : Type uC) [Group C]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (z : C →* G) (ω χ : C →* ℂˣ),
    Classification.HasScalarCharacter ρ z ω →
    IsGeneralizedEigencharacter (ρ.comp z) χ → χ = ω) ∧
  (∀ (G : Type uG) [Group G] (C : Type uC) [Group C]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ G V) (z : C →* G) (ω χ : C →* ℂˣ),
    Classification.HasScalarCharacter ρ z ω →
    (IsGeneralizedEigencharacter (ρ.comp z) χ ↔ χ = ω))

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Ambient scalar action descends to the actual normalized Jacquet quotient,
and every generalized split-centre character restricts to that character. -/
def NormalizedJacquetScalarCompatibility : Prop :=
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (ω : F.Carrierˣ →* ℂˣ),
    Classification.HasScalarCharacter ρ GeneralLinear.scalar ω →
    Classification.HasScalarCharacter (T.normalizedJacquet B ρ)
      (B.scalarLevi F.Carrier) ω ∧
    ∀ (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter (T.splitCentreJacquet B ρ) χ →
      χ.comp (Pi.constMonoidHom (Fin B.length) F.Carrierˣ) = ω

end PadicField.TopologicalData

end Langlands
