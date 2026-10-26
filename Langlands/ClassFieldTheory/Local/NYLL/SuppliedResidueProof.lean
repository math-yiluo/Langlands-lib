import Langlands.ClassFieldTheory.Local.NYLL.SuppliedResidueStatement

/-! # Supplied residue congruence -/

namespace Langlands.LocalClassField.NYLL

universe u

/-- Equality in the supplied residue field is measured by the supplied
discrete valuation, for arbitrary supplied topological data. -/
theorem suppliedResidueCongruence : SuppliedResidueCongruenceStatement.{u} := by
  intro p _ F T x y
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit (x - y) ↔
    T.discreteValuation ((x : F.Carrier) - (y : F.Carrier)) < 1
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change ValuativeRel.valuation F.Carrier ((x : F.Carrier) - (y : F.Carrier)) < 1 ↔
    e (ValuativeRel.valuation F.Carrier ((x : F.Carrier) - (y : F.Carrier))) < 1
  rw [← map_one e]
  exact e.strictMono.lt_iff_lt.symm

end Langlands.LocalClassField.NYLL
