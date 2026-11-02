/-
Ported from `Theorems/Thm_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Langlands.AnthropicFLT.P2M.Sol.S_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.ker_baseChange_le_range_and_finrank_eq_of_field_extension
    {R : Type u} [CommRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1))
    {F : Type u} [AddCommGroup F] [Module R F] (Θ : F →ₗ[R] C 0)
    (K : Type u) [Field K] [Algebra R K] (K' : Type u) [Field K'] [Algebra R K'] [Algebra K K']
    [IsScalarTower R K K'] (r : ℕ)
    (h1 : ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange K') ≤ LinearMap.range ((d i).baseChange K'))
    (h2 : LinearMap.ker ((d 0).baseChange K') ≤ LinearMap.range (Θ.baseChange K'))
    (h3 : Module.finrank K' (LinearMap.ker ((d 0).baseChange K')) = r) :
    (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K)) ∧
    LinearMap.ker ((d 0).baseChange K) ≤ LinearMap.range (Θ.baseChange K) ∧
    Module.finrank K (LinearMap.ker ((d 0).baseChange K)) = r :=
  P2MW.S_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension.solution C d Θ K K' r h1 h2 h3
