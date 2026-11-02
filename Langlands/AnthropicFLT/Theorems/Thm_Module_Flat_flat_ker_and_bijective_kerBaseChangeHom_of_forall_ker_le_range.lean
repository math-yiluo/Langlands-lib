/-
Ported from `Theorems/Thm_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range
    {R : Type u} [CommRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hex : ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) :
    Module.Flat R (LinearMap.ker (d 0)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A) :=
  P2MW.S_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range.solution C d hdd n hbd hex
