/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 121, 13 November 2026 UTC:
Extract only the proof of M007.005 from
Nyll/GaloisCohomology/ProfiniteIntegers/TopologicalGeneration.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published TopologicalGeneration
Statements module. Prove its closed proposition by introducing all six
internal binders, then keep the original proof body except one line:
the rewrite by topologicallyGenerates_iff_dense (M007.002, not yet
proved in the Library) and dense_iff_closure_eq is replaced by the
rewrites TopologicallyGenerates, SetLike.ext'_iff,
Subgroup.topologicalClosure_coe and Subgroup.coe_top, i.e. the original
M007.002 proof without its final density step. Preserve universes u
and v and the explicit family φ. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.Statements

/-!
# The canonical family topologically generates its closed generated subgroup

The exact proof of the published closed assertion M007.005: for any family
`φ : A → G` in a topological group, the range of the canonical family
`closedSubgroupGeneratedMap φ` topologically generates the subgroup
underlying `closedSubgroupGenerated (Set.range φ)`.
-/

namespace Langlands.NYLL.ClassFormation

open Set
open scoped Topology Pointwise

universe u v

/-- The canonical family topologically generates its closed generated
subgroup. -/
theorem closedSubgroupGeneratedMap_topologicallyGenerates :
    closedSubgroupGeneratedMap_topologicallyGeneratesStatement.{u, v} := by
  intro G _ _ _ A φ
  let K : ClosedSubgroup G := closedSubgroupGenerated (G := G) (Set.range φ)
  let φK : A → (K : Subgroup G) := closedSubgroupGeneratedMap (G := G) φ
  let L : Subgroup (K : Subgroup G) := Subgroup.closure (Set.range φK)
  have hmap :
      Subgroup.map (K : Subgroup G).subtype L =
        Subgroup.closure (Set.range φ) := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro y ⟨a, rfl⟩
      exact Subgroup.subset_closure ⟨a, rfl⟩
    · rw [Subgroup.closure_le]
      rintro y ⟨a, rfl⟩
      change φ a ∈ Subgroup.map (K : Subgroup G).subtype L
      exact ⟨φK a, Subgroup.subset_closure ⟨a, rfl⟩, rfl⟩
  have himage :
      ((Subtype.val : ↥(K : Subgroup G) → G) ''
          ((L : Subgroup ↥(K : Subgroup G)) : Set ↥(K : Subgroup G))) =
        ((Subgroup.map (K : Subgroup G).subtype L : Subgroup G) : Set G) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      exact ⟨z, hz, hzy⟩
  rw [TopologicallyGenerates, SetLike.ext'_iff, Subgroup.topologicalClosure_coe,
    Subgroup.coe_top]
  ext y
  constructor
  · intro _
    simp only [mem_univ]
  · intro _
    change y ∈ closure ((L : Subgroup K) : Set K)
    rw [closure_subtype]
    change (y : G) ∈
      closure
        (((Subtype.val : ↥(K : Subgroup G) → G) ''
          ((L : Subgroup ↥(K : Subgroup G)) : Set ↥(K : Subgroup G))))
    rw [himage, hmap]
    change (y : G) ∈
      ((Subgroup.closure (Set.range φ)).topologicalClosure : Set G)
    exact y.2

end Langlands.NYLL.ClassFormation
