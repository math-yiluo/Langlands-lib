import Mathlib.Topology.Algebra.Nonarchimedean.Basic

open Topology

namespace Langlands

/-- Subgroups inherit the nonarchimedean identity-neighborhood basis. -/
instance subgroupNonarchimedean {G : Type*} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] (S : Subgroup G) : NonarchimedeanGroup S where
  is_nonarchimedean U hU := by
    rw [nhds_subtype_eq_comap] at hU
    obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
    obtain ⟨K, hKV⟩ := NonarchimedeanGroup.is_nonarchimedean V hV
    refine ⟨K.comap S.subtype continuous_subtype_val, ?_⟩
    exact (Set.preimage_mono hKV).trans hVU

end Langlands
