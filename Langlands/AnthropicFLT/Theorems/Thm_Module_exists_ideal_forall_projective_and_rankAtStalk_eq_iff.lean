/-
Ported from `Theorems/Thm_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open scoped TensorProduct

theorem Module.exists_ideal_forall_projective_and_rankAtStalk_eq_iff
    (A : Type uz) [CommRing A] (M : Type uz) [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ)
    (hr : ∀ p : PrimeSpectrum A,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M) ≤ r) :
    ∃ 𝔞 : Ideal A, ∀ (B : Type uz) [CommRing B] [Algebra A B],
      (Module.Projective B (B ⊗[A] M) ∧ ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] M) q = r) ↔
        ∀ a ∈ 𝔞, algebraMap A B a = 0 :=
  P2MW.S_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff.solution A M r hr
