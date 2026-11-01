import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Exponents.Chambers

/-! # Rank-weighted real parts of actual cuspidal tensors -/

namespace Langlands

open scoped BigOperators

universe uF uV

/-- Actual supercuspidal factors admit positive real unitarizing twists. Their
original scalar characters have negative rank-weighted real exponents, and the
actual external tensor has the corresponding split-centre real part. -/
def CuspidalTensorRealPartsStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
    (C : ∀ i, GeneralLinear.SupercuspidalRep.{uF,uV}
      (F := F.Carrier) (n := B.size i)),
    ∃ (t : Fin B.length → ℝ) (c : Fin B.length → (F.Carrierˣ →* ℂˣ)),
      (∀ i, IsUnitarizable
        (realPowerTwist (T.determinantNorm (B.size i)) (t i)
          (C i).obj.representation)) ∧
      (∀ i, Classification.HasScalarCharacter (C i).obj.representation
        GeneralLinear.scalar (c i)) ∧
      (∀ i (a : F.Carrierˣ), ‖(c i a : ℂ)‖ =
        T.normalizedAbs (a : F.Carrier) ^ (-((B.size i : ℝ) * t i))) ∧
      let χ := ∏ i, (c i).comp
        (Pi.evalMonoidHom (fun _ : Fin B.length => F.Carrierˣ) i)
      Classification.HasScalarCharacter
        (B.blockTensor (fun i => (C i).obj.representation))
        (B.blockScalarLevi F.Carrier) χ ∧
      T.IsRealPartOf χ (fun i => -((B.size i : ℝ) * t i))

end Langlands
