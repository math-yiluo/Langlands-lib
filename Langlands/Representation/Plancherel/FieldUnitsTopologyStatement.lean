import Langlands.Representation.Plancherel.LocalFieldUnits
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Topology of the actual normalized local-field maps

These conclusions concern the supplied local-field topology and the standard
unit-group topology. They are deductions to prove, rather than additional
structural assumptions of the Plancherel framework.
-/

open scoped NNReal

namespace Langlands.Plancherel

universe uF

/-- The actual normalized absolute value is continuous, and its units restriction
and source-positive integer order are locally constant and continuous. -/
def FieldUnitsTopologyStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    Continuous (LocalField.residueNormalizedAbsoluteValue F) ∧
      IsLocallyConstant (fieldOrderUnits F) ∧
      Continuous (fieldOrderUnits F) ∧
      IsLocallyConstant (fieldNormUnits F) ∧
      Continuous (fieldNormUnits F)

end Langlands.Plancherel
