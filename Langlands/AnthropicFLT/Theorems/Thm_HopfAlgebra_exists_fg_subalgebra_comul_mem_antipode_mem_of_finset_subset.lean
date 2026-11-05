/-
Ported from `Theorems/Thm_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (s : Finset H) (hs : (↑s : Set H) ⊆ K) :
    ∃ K₀ : Subalgebra k H, K₀ ≤ K ∧ K₀.FG ∧ (↑s : Set H) ⊆ K₀ ∧
      (∀ x ∈ K₀, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K₀, ∃ b ∈ K₀, t = a ⊗ₜ[k] b}) ∧
      (∀ x ∈ K₀, HopfAlgebra.antipode k x ∈ K₀) := by
  exact _root_.P2MW.S_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset.solution K hΔ hS s hs
