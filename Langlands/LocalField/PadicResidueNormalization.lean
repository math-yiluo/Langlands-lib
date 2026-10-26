import Langlands.LocalField.ResidueNormalization
import Langlands.LocalFactor.FML.Conductors
import Langlands.LocalField.Normalization.Proof

/-! # Supplied p-adic specialization of the general residue normalization -/

universe u

namespace Langlands.FML.Padic

variable {p : ℕ} [Fact p.Prime] {F : Langlands.PadicField.{u} p}
  (T : F.TopologicalData)

/-- The source-standard order agrees with the host integer order away from zero. -/
theorem ord_eq_host_ord_of_ne_zero {x : F.Carrier} (hx : x ≠ 0) :
    ord T x = (T.ord x : WithTop ℤ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have h := FML.ord_of_ne_zero F.Carrier hx
  change ord T x =
    ((-WithZero.log (normalizedValuation T x) : ℤ) : WithTop ℤ) at h
  simpa only [normalizedValuation_eq_discreteValuation,
    PadicField.TopologicalData.ord] using h

end Langlands.FML.Padic

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The generic and host cardinalities refer to the same actual residue field. -/
theorem general_residueCardinality_eq :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    LocalField.residueCardinality F.Carrier = T.residueCardinality := by
  rfl

/-- Pointwise specialization with precisely the topology and valuation supplied by `T`.
The zero case uses the absolute-value zero law and the existing host zero law. -/
theorem residueNormalizedAbsoluteValue_eq_normalizedAbs (x : F.Carrier) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    LocalField.residueNormalizedAbsoluteValue F.Carrier x = T.normalizedAbs x := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  by_cases hx : x = 0
  · subst x
    rw [map_zero, T.normalizedAbs_zero]
  · rw [LocalField.residueNormalizedAbsoluteValue_of_ord_eq F.Carrier
      (FML.Padic.ord_eq_host_ord_of_ne_zero T hx), T.normalizedAbs_of_ne_zero hx,
      T.general_residueCardinality_eq]

end Langlands.PadicField.TopologicalData
