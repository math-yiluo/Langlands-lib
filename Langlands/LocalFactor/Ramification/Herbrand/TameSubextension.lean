import Langlands.LocalFactor.Ramification.Herbrand.SubextensionProof

/-!
# Herbrand rescaling across a tame totally ramified subextension
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open LocalClassField Weil.Local

/-- For an actual tame totally ramified extension of degree `m`, the
relative inverse Herbrand function is multiplication by `m` on the
nonnegative half-line. All strictly positive upper groups agree under
inclusion with this change of index. -/
def TameSubextensionHerbrandStatement.{u} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{u} p) (E : FiniteIntermediateExtension K.Carrier),
    let L := E.asPadicField (p := p)
    let ι := intermediateEmbedding K E
    let m := extensionDegree K L ι
    extensionResidueDegree K L ι = 1 → ¬ p ∣ m →
      (∀ v : ℝ, 0 ≤ v → relativeHerbrandPsi E v = (m : ℝ) * v) ∧
      ∀ v : ℝ, 0 < v →
        (VirtualRepresentation.LocalWeil.Ramification.upperGroup L ((m : ℝ) * v)).map
          (intermediateWeilMap K E).toMonoidHom =
            VirtualRepresentation.LocalWeil.Ramification.upperGroup K v

end Langlands.Ramification.HerbrandBridge
