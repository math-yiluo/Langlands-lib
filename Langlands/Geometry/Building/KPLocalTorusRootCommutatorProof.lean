import Langlands.Geometry.Building.KPLocalTorusRootCommutatorReduction
import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesProof

/-! # Positive-depth torus action on root-group filtrations over `K = F^ur`

Proof of `KPLocalTorusRootCommutatorStatement`: the reduction
`kpLocalTorusRootCommutator_of_valuedRankOneCoordinates` applied to the published existence
of valued rank-one coordinates, `quasiSplitValuedRankOneCoordinates`.
-/

universe u

namespace Langlands.Geometry.Building

/-- Positive-depth torus action on the root-group filtrations of quasi-split building data
over `K = F^ur` (KP Lemma 7.2.3 over `K`): for `0 < r`, `t ∈ Z(K)` congruent to `1` at depth
`r` under every geometric character of `Z`, `z = j(t)` and `u ∈ U_{a,x,s}`, the commutator
`z u z⁻¹ u⁻¹` lies in the block `U_{a,x,r+s} · U_{2a,x,r+s}`. -/
theorem kpLocalTorusRootCommutator : KPLocalTorusRootCommutatorStatement.{u} :=
  kpLocalTorusRootCommutator_of_valuedRankOneCoordinates quasiSplitValuedRankOneCoordinates

end Langlands.Geometry.Building
