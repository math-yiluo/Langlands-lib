import Langlands.ClassFieldTheory.Local.Supplied.SuppliedUniformityStatement

/-!
# Compatibility of the supplied additive right uniformity
-/

namespace Langlands.LocalClassField.UniverseZero

universe u

/-- The named supplied right uniformity retains the topology and makes addition uniform. -/
theorem suppliedUniformityCompatibility :
    SuppliedUniformityCompatibilityStatement.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  constructor
  · rfl
  · exact isUniformAddGroup_of_addCommGroup (G := F.Carrier)

end Langlands.LocalClassField.UniverseZero
