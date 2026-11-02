/-
Ported from `Theorems/Thm_Module_Projective_exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_Projective_exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v
open TensorProduct

theorem Module.Projective.exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot
    (B : Type u) [CommRing B] (M : Type v) [AddCommGroup M] [Module B M]
    [Module.Finite B M] [Module.Projective B M] (x : M) :
    ∃ J : Ideal B, J.FG ∧ ∀ (A : Type u) [CommRing A] (φ : B →+* A),
      (letI : Algebra B A := φ.toAlgebra; ((1 : A) ⊗ₜ[B] x : A ⊗[B] M) = 0) ↔ Ideal.map φ J = ⊥ :=
  P2MW.S_Module_Projective_exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot.solution B M x
