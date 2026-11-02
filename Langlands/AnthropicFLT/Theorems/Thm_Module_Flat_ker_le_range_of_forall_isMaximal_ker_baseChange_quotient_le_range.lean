/-
Ported from `Theorems/Thm_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal] (i : ℕ),
      LinearMap.ker ((d (i + 1)).baseChange (R ⧸ 𝔪)) ≤ LinearMap.range ((d i).baseChange (R ⧸ 𝔪))) :
    ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i) :=
  P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.solution C d hdd n hbd hfin hfib
