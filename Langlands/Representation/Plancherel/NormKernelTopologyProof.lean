import Langlands.Representation.Plancherel.NormKernelTopologyStatement
import Langlands.Topology.CompactNormCharacter
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! # Topology of the common kernel of continuous positive characters -/

open scoped NNReal
open Topology

namespace Langlands.Plancherel

universe uG uI

/-- The common norm kernel is open and closed and contains all compact
subgroups and the abstract commutator subgroup. -/
theorem commonNormKernelTopology : CommonNormKernelTopologyStatement.{uG, uI} := by
  intro G _ _ _ _ I ν hν
  have hcompact (K : Subgroup G) (hK : IsCompact (K : Set G)) :
      K ≤ commonNormKernel ν := by
    intro g hg
    apply (mem_commonNormKernel ν g).mpr
    intro i
    exact Langlands.RankinSelberg.LastRowReduction.eq_one_of_isCompact
      (ν i) (hν i) K hK hg
  obtain ⟨K, hK, _⟩ :=
    Langlands.compactOpenSubgroupBasis G Set.univ Filter.univ_mem
  have hopen : IsOpen (commonNormKernel ν : Set G) :=
    Subgroup.isOpen_mono (hcompact K.toSubgroup hK) K.isOpen
  refine ⟨hopen, ?_, hcompact, ?_⟩
  · simp only [commonNormKernel, Subgroup.coe_iInf]
    exact isClosed_iInter fun i => isClosed_eq (hν i) continuous_const
  · change ⁅(⊤ : Subgroup G), ⊤⁆ ≤ commonNormKernel ν
    apply Subgroup.commutator_le.mpr
    intro g _ h _
    apply (mem_commonNormKernel ν _).mpr
    intro i
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _

end Langlands.Plancherel
