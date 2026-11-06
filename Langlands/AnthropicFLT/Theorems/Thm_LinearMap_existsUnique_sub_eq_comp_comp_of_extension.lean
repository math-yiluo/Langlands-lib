/-
Ported from `Theorems/Thm_LinearMap_existsUnique_sub_eq_comp_comp_of_extension.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_existsUnique_sub_eq_comp_comp_of_extension
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w w' x

theorem LinearMap.existsUnique_sub_eq_comp_comp_of_extension
    {R : Type u} [CommRing R]
    {K : Type v} {M : Type w} {M' : Type w'} {E : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup E] [Module R E]
    (ϑ : K →ₗ[R] M) (θ : M →ₗ[R] E) (ϑ' : K →ₗ[R] M') (θ' : M' →ₗ[R] E)
    (hθ : Function.Surjective θ) (hex : LinearMap.range ϑ = LinearMap.ker θ)
    (hϑ' : Function.Injective ϑ') (hex' : LinearMap.range ϑ' = LinearMap.ker θ')
    (α β : M →ₗ[R] M') (hK : α ∘ₗ ϑ = β ∘ₗ ϑ) (hE : θ' ∘ₗ α = θ' ∘ₗ β) :
    ∃! γ : E →ₗ[R] K, α - β = ϑ' ∘ₗ γ ∘ₗ θ :=
  P2MW.S_LinearMap_existsUnique_sub_eq_comp_comp_of_extension.solution ϑ θ ϑ' θ' hθ hex hϑ' hex' α β hK hE
