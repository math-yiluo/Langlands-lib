import Langlands.LocalField.ResidueNormalization

/-! # The topology of the residue-normalized metric -/

namespace Langlands.LocalField

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The distance given by the residue-normalized absolute value of differences
is an ultrametric and induces the given field topology. -/
def ResidueNormalizedMetricStatement : Prop :=
  ∃ m : MetricSpace F,
    m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace F› ∧
    (∀ x y : F, @dist F m.toDist x y = residueNormalizedAbsoluteValue F (x - y)) ∧
    @IsUltrametricDist F m.toDist

end Langlands.LocalField
