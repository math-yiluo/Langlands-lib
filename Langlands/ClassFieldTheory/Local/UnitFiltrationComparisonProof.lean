import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.ClassFieldTheory.Local.FiniteConductorStatement
import Langlands.LocalField.Normalization.Proof
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof

/-!
# The two unit filtrations agree

The quotient-kernel filtration `T.unitFiltration n` (integer units congruent to `1` modulo
the `n`th power of the maximal ideal) and the valuation filtration `T.principalUnits n`
(units `u` with `v(u) = 1` and `v(u - 1) ≤ exp(-n)`) are the same subgroups of `Fˣ`,
including level zero.
-/

noncomputable section

open scoped WithZero

namespace Langlands.PadicField.TopologicalData

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The chosen uniformizer, as an element of the integer ring. -/
def integralUniformizer : T.Integers :=
  ⟨T.uniformizer, (T.mem_integers_iff_discreteValuation_le_one _).mpr (by
    rw [T.discreteValuation_uniformizer]; norm_num)⟩

theorem integralUniformizer_coe : (T.integralUniformizer : F.Carrier) = T.uniformizer := rfl

theorem maximalIdeal_eq_span_integralUniformizer :
    IsLocalRing.maximalIdeal T.Integers = Ideal.span {T.integralUniformizer} := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit x ↔ x ∈ Ideal.span {T.integralUniformizer}
  rw [T.filtrationValuationIntegers.isUnit_iff_valuation_eq_one]
  rw [← SetLike.mem_coe,
    T.filtrationValuationIntegers.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
  change T.discreteValuation x.val ≠ 1 ↔
    T.discreteValuation x.val ≤ T.discreteValuation T.integralUniformizer.val
  rw [T.integralUniformizer_coe, T.discreteValuation_uniformizer]
  have hle := T.filtrationValuationIntegers.map_le_one x
  have hstep : T.discreteValuation x.val < 1 ↔
      T.discreteValuation x.val ≤ WithZero.exp (-1) := by
    simpa [← WithZero.exp_add] using
      (WithZero.lt_mul_exp_iff_le (x := T.discreteValuation x.val)
        (y := WithZero.exp (-1)) WithZero.exp_ne_zero)
  rw [← hstep]
  exact ⟨fun h => lt_of_le_of_ne hle h, fun h => h.ne⟩

theorem integralUniformizer_irreducible : Irreducible T.integralUniformizer := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    T.maximalIdeal_eq_span_integralUniformizer

end Langlands.PadicField.TopologicalData

