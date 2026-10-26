import Langlands.Representation.Classification.RelativeRegularComparisonStatement
import Langlands.Representation.Twist.LeviComplexPower

/-! # Imaginary determinant twists and whole-Levi analytic predicates -/

noncomputable section

namespace Langlands

universe uF uV

/-- Imaginary determinant twisting preserves and reflects the existing
whole-product analytic predicates, with every Borel Haar realization. -/
def LeviImaginaryTwistModCenterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : GeneralLinear.BlockShape n)
    (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) (u : Fin B.length → ℝ),
    let σu := Rep.of
      (T.leviComplexPowerTwist B (fun i => Complex.I * (u i : ℂ)) σ.ρ)
    (RelativeRegularComparison.IsLeviSquareIntegrable T B σu ↔
      RelativeRegularComparison.IsLeviSquareIntegrable T B σ) ∧
    (RelativeRegularComparison.IsLeviTempered T B σu ↔
      RelativeRegularComparison.IsLeviTempered T B σ)

end Langlands
