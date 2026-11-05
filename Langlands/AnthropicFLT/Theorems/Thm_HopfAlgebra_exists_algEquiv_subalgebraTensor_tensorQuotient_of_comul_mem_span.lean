/-
Ported from `Theorems/Thm_HopfAlgebra_exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span
    {k : Type u} [CommRing k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) :
    ∃ β : (H ⊗[↥K] H) ≃ₐ[H]
        (H ⊗[k] (H ⧸ Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0})),
      ∀ h₁ h₂ : H, β (h₁ ⊗ₜ[↥K] h₂) =
        (h₁ ⊗ₜ[k] (1 : H ⧸ Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0})) *
          Algebra.TensorProduct.map (AlgHom.id k H)
            (Ideal.Quotient.mkₐ k (Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}))
            (Coalgebra.comul (R := k) h₂) := P2MW.S_HopfAlgebra_exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span.solution K hΔ
