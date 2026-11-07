import Langlands.Representation.Classification.TadicExhaustionAssembly
import Langlands.Representation.Classification.TadicExhaustionReductionStatement

/-! Proof of `TadicExhaustionReduction` by Tadić's induction (Theorem A.10). -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Tadić's exhaustion argument: the three ingredient statements imply the exhaustion. -/
theorem tadicExhaustionReduction : TadicExhaustionReduction.{uF, uV} F T :=
  fun hP hSU hHC => tadicUnitaryDualExhaustion_of_ingredients hP hSU hHC

end Langlands.Classification
