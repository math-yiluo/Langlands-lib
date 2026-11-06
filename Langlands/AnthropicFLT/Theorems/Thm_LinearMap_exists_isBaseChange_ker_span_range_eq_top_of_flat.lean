/-
Ported from `Theorems/Thm_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem LinearMap.exists_isBaseChange_ker_span_range_eq_top_of_flat
    {B : Type u} [CommRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
    {M : Type v} [AddCommGroup M] [Module B M]
    {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M)
    (p' : (Fin r → B') →ₗ[B'] M') (hp' : ∀ v : Fin r → B, p' (fun i => algebraMap B B' (v i)) = μ (p v)) :
    ∃ g : ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker p'),
      (∀ (s : ↥(LinearMap.ker p)) (i : Fin r), ((g s : ↥(LinearMap.ker p')) : Fin r → B') i = algebraMap B B' ((s : Fin r → B) i)) ∧
      IsBaseChange B' g ∧
      Submodule.span B' (Set.range g) = ⊤ :=
  P2MW.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat.solution μ hμ p p' hp'
