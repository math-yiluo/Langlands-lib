/-
Ported from `Theorems/Thm_MvPolynomial_exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem MvPolynomial.exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero
    (B : Type*) [CommRing B] {m : ℕ} (c : Fin m → MvPolynomial (Fin m) B)
    (hc : ∑ j, c j * MvPolynomial.X j = 0) :
    ∃ e : Fin m → Fin m → MvPolynomial (Fin m) B,
      (∀ j k, e j k = -e k j) ∧ (∀ j, e j j = 0) ∧ ∀ j, c j = ∑ k, e j k * MvPolynomial.X k :=
  P2MW.S_MvPolynomial_exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero.solution B c hc
