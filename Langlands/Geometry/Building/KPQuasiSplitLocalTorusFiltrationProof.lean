import Langlands.Geometry.Building.KPLocalCentralizerTorusFiltrationClauses
import Langlands.Geometry.Building.KPLocalCorootComponentProof
import Langlands.Geometry.Building.KPLocalTorusRootCommutatorProof

/-! # The torus filtration of quasi-split building data over `K = F^ur`

The three clauses of `QuasiSplitLocalTorusFiltrationStatement` follow from the
published coroot component formula and positive-depth torus/root commutator theorem.
-/

universe u

namespace Langlands.Geometry.Building

/-- KP Lemma 7.2.3 over `K = F^ur`, together with root compatibility and normalizer
stability, for the published torus filtration of quasi-split building data. -/
theorem quasiSplitLocalTorusFiltration : QuasiSplitLocalTorusFiltrationStatement.{u} :=
  quasiSplitLocalTorusFiltration_of_coroot_of_torusRoot
    kpLocalCorootComponent kpLocalTorusRootCommutator

end Langlands.Geometry.Building
