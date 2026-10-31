import Langlands.Geometry.Analytic.AtlasTopology.QuasinetProperties
import Mathlib.Data.Set.Finite.Lattice

/-! # Compact containment in directed quasinets -/

universe u v

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u} {ι : Type v} [Nonempty ι]
  {U : ι → Set X}

/-- A finite subfamily of a nonempty directed family has a single upper member. -/
theorem exists_sUnion_subset_of_finite (hd : Directed (· ⊆ ·) U)
    {σ : Set (Set X)} (hσ : σ.Finite) (hσU : σ ⊆ Set.range U) :
    ∃ i, ⋃₀ σ ⊆ U i := by
  revert hσU
  induction σ, hσ using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨Classical.choice ‹Nonempty ι›, by simp⟩
  | @insert V σ _ _ ih =>
    intro hσU
    obtain ⟨i, rfl⟩ := hσU (Set.mem_insert V σ)
    obtain ⟨j, hj⟩ := ih (fun W hW => hσU (Set.mem_insert_of_mem _ hW))
    obtain ⟨q, hiq, hjq⟩ := hd i j
    refine ⟨q, ?_⟩
    rw [Set.sUnion_insert]
    exact Set.union_subset hiq (hj.trans hjq)

variable [TopologicalSpace X]

/-- The finite quasinet neighborhood can be enlarged to one original member. -/
theorem IsQuasinet.exists_mem_nhds_of_directed
    (hU : IsQuasinet (Set.range U)) (hd : Directed (· ⊆ ·) U) (x : X) :
    ∃ i, U i ∈ 𝓝 x := by
  obtain ⟨σ, hσ, hσU, _, hn⟩ := hU x
  obtain ⟨i, hi⟩ := exists_sUnion_subset_of_finite hd hσ hσU
  exact ⟨i, mem_of_superset hn hi⟩

/-- Interiors of the original directed quasinet members cover the space. -/
theorem IsQuasinet.exists_mem_interior_of_directed
    (hU : IsQuasinet (Set.range U)) (hd : Directed (· ⊆ ·) U) (x : X) :
    ∃ i, x ∈ interior (U i) := by
  obtain ⟨i, hi⟩ := hU.exists_mem_nhds_of_directed hd x
  exact ⟨i, mem_interior_iff_mem_nhds.mpr hi⟩

/-- Every compact subset lies in the interior of one original member.
No Hausdorff assumption on the ambient space is needed. -/
theorem IsQuasinet.exists_subset_interior_of_isCompact
    (hU : IsQuasinet (Set.range U)) (hd : Directed (· ⊆ ·) U)
    {S : Set X} (hS : IsCompact S) :
    ∃ i, S ⊆ interior (U i) := by
  apply hS.elim_directed_cover (fun i => interior (U i)) (fun _ => isOpen_interior)
  · intro x _
    obtain ⟨i, hi⟩ := hU.exists_mem_interior_of_directed hd x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro i j
    obtain ⟨q, hiq, hjq⟩ := hd i j
    exact ⟨q, interior_mono hiq, interior_mono hjq⟩

/-- In particular every compact subset is contained in one original member. -/
theorem IsQuasinet.exists_subset_of_isCompact
    (hU : IsQuasinet (Set.range U)) (hd : Directed (· ⊆ ·) U)
    {S : Set X} (hS : IsCompact S) :
    ∃ i, S ⊆ U i := by
  obtain ⟨i, hi⟩ := hU.exists_subset_interior_of_isCompact hd hS
  exact ⟨i, hi.trans interior_subset⟩

end Langlands.Analytic.AtlasTopology
