import Langlands.Global.ArchimedeanConjugationNeighborhoodStatement

/-! # Uniform compact conjugation near the identity -/

universe u
open Filter Topology
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Compactness makes the conjugation neighborhood uniform in the compact element. -/
theorem compactConjugationNeighborhood : CompactConjugationNeighborhoodStatement K n := by
  intro U hU
  have h : ∀ᶠ y : InfiniteAdelicGL K n in 𝓝 1,
      ∀ k ∈ (standardInfiniteCompact K n : Set (InfiniteAdelicGL K n)),
        k * y * k⁻¹ ∈ U := by
    apply (isCompact_standardInfiniteCompact K n).eventually_forall_of_forall_eventually
    intro k _
    have hc : Continuous (fun z : InfiniteAdelicGL K n × InfiniteAdelicGL K n =>
        z.2 * z.1 * z.2⁻¹) :=
      (continuous_snd.mul continuous_fst).mul continuous_snd.inv
    exact hc.continuousAt.eventually (by simpa using hU)
  rcases mem_nhds_iff.mp h with ⟨V, hV, hVo, hV1⟩
  refine ⟨V, hVo.mem_nhds hV1, hVo, ?_, ?_⟩
  · intro y hy
    simpa using hV hy 1 (Subgroup.one_mem (standardInfiniteCompact K n))
  · rintro x ⟨k, y, hy, rfl⟩
    exact hV hy k.val k.property

end Langlands.Global.ArchimedeanGL
