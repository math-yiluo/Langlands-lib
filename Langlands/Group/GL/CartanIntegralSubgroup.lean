import Langlands.Group.GL.CartanQuotientDefinitions

/-! # The integral subgroup in Cartan coordinates -/

noncomputable section

namespace Langlands.ProductLeviTempered

open GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

theorem discreteValuation_integer : T.discreteValuation.integer = T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  ext x
  rw [Valuation.mem_integer_iff]
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  change e (ValuativeRel.valuation F.Carrier x) ≤ 1 ↔ ValuativeRel.valuation F.Carrier x ≤ 1
  rw [← map_one e]
  exact e.strictMono.le_iff_le

theorem maximalCompact_eq (N : ℕ) :
    letI := T.valuativeRel
    CartanQuotient.maximalCompact T N =
      Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) N := by
  let := T.valuativeRel
  unfold CartanQuotient.maximalCompact Iwasawa.integralRange
  rw [discreteValuation_integer]

end Langlands.ProductLeviTempered
