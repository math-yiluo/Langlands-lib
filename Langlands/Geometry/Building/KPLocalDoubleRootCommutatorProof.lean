import Langlands.Geometry.Building.RankOneDoubledInputCoroot
import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesProof

/-! # Proof of the doubled-root commutator estimate over `K = F^ur` (KP 7.1.1, 7.2.3) -/

universe u

namespace Langlands.Geometry.Building

/-- The doubled-root commutator estimate over `K = F^ur`: the `Z`-component of
`u'⁻¹ u u' u⁻¹` lies in `Z(K)_{2r}` whenever one of the nontrivial inputs lies in the doubled
root group (quasi-split proof of KP Proposition 7.1.1, proof of KP Lemma 7.2.3). -/
theorem kpLocalDoubleRootCommutator : KPLocalDoubleRootCommutatorStatement.{u} :=
  kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates quasiSplitValuedRankOneCoordinates

end Langlands.Geometry.Building
