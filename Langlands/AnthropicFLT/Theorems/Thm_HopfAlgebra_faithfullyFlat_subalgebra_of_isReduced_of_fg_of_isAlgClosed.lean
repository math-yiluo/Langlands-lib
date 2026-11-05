/-
Ported from `Theorems/Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (hfg : K.FG) [IsReduced ↥K] :
    Module.FaithfullyFlat ↥K H := by
  exact _root_.P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed.solution K hΔ hS hfg
