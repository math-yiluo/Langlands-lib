import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Normed compact-restriction coordinates for continuous functions -/

noncomputable section
universe u v
open scoped Topology
open Filter Topology TopologicalSpace
set_option autoImplicit false

namespace Langlands.Analysis

variable (X : Type u) [TopologicalSpace X]
variable (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- All compact restrictions, as a continuous real linear map. -/
def compactRestrictionCoordinates :
    C(X, F) →L[ℝ] (∀ s : Compacts X, C(s, F)) :=
  ContinuousLinearMap.pi (fun s =>
    ContinuousMap.compCLM ℝ F
      (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))

@[simp]
theorem compactRestrictionCoordinates_apply (f : C(X, F)) (s : Compacts X) (x : s) :
    compactRestrictionCoordinates X F f s x = f x := rfl

theorem tendsto_compactRestrictionCoordinates_iff
    {ι : Type*} {l : Filter ι} {f : ι → C(X, F)} {g : C(X, F)} :
    Tendsto (fun i => compactRestrictionCoordinates X F (f i)) l
      (𝓝 (compactRestrictionCoordinates X F g)) ↔ Tendsto f l (𝓝 g) := by
  rw [tendsto_pi_nhds, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  constructor
  · intro h s hs
    let K : Compacts X := ⟨s, hs⟩
    exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
      (ContinuousMap.tendsto_iff_tendstoUniformly.mp (h K))
  · intro h s
    rw [ContinuousMap.tendsto_iff_tendstoUniformly]
    exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp (h s s.isCompact)

/-- The compact-open topology is exactly the topology induced by all normed
compact-restriction coordinates. -/
theorem isEmbedding_compactRestrictionCoordinates :
    IsEmbedding (compactRestrictionCoordinates X F) := by
  refine ⟨isInducing_iff_nhds.mpr (fun f => le_antisymm ?_ ?_), ?_⟩
  · exact (compactRestrictionCoordinates X F).continuous.continuousAt.le_comap
  · exact (tendsto_compactRestrictionCoordinates_iff X F).mp tendsto_comap
  · intro f g h
    ext x
    let K : Compacts X := {x}
    exact congrArg (fun q => q K (⟨x, by simp [K]⟩ : K)) h

end Langlands.Analysis
