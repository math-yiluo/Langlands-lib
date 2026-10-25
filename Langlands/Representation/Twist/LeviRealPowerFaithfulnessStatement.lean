import Langlands.Representation.Twist.LeviRealPower
import Langlands.LocalField.Uniformizer

/-! Faithfulness of real determinant exponents, including the central direction. -/
noncomputable section

namespace Langlands

universe uF

/-- Uniformizer evaluation and faithfulness already on the block-scalar subgroup. -/
def LeviRealPowerFaithfulnessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : GeneralLinear.BlockShape n),
    (∀ (t : Fin B.length → ℝ) (i : Fin B.length),
      (T.leviRealPowerCharacter B t
        (B.blockScalarLevi F.Carrier
          (Pi.mulSingle i (LocalFactor.PadicAbelian.uniformizerUnit T))) : ℂ) =
        (((T.residueCardinality : ℝ) ^ (-(B.size i : ℝ) * t i) : ℝ) : ℂ)) ∧
    Function.Injective (fun t : Fin B.length → ℝ =>
      (T.leviRealPowerCharacter B t).comp (B.blockScalarLevi F.Carrier)) ∧
    Function.Injective (T.leviRealPowerCharacter B)

end Langlands
