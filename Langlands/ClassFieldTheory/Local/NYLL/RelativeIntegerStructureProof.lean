import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureStatement

/-! Relative integral closure and finiteness for the supplied integer rings. -/

namespace Langlands.LocalClassField.NYLL

universe u v

/-- The exact supplied relative integer structures satisfy closure and finiteness. -/
theorem relativeIntegerStructure : RelativeIntegerStructureStatement.{u,v} := by
  intro p hp F E hFE hbase hfinite T S
  let := PadicField.TopologicalData.relativeIntegerAlgebra T S
  let := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := E) T
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := T.integerAlgebra
  let := S.integerAlgebra
  let := Algebra.compHom E.Carrier (algebraMap A (Padic p))
  let := PadicField.TopologicalData.relativeBaseIntegerTower T S
  let : IsScalarTower A T.Integers E.Carrier :=
    IsScalarTower.of_algebraMap_eq fun x =>
      IsScalarTower.algebraMap_apply (Padic p) F.Carrier E.Carrier x.val
  let := T.integers_finite
  let := S.integers_finite
  let := S.integers_isIntegralClosure
  exact ⟨IsIntegralClosure.tower_top (R := A),
    Module.Finite.of_restrictScalars_finite A T.Integers S.Integers⟩

end Langlands.LocalClassField.NYLL
