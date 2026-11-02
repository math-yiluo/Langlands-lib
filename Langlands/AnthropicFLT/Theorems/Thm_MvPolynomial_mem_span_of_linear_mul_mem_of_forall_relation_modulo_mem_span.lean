/-
Ported from `Theorems/Thm_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open MvPolynomial

theorem MvPolynomial.mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span
    (n m g : ℕ) (K : Type uz) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m) (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcol : ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m →
      ℓ * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F))
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i ∈ Ideal.span {ℓ} →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
        {l : Fin g → MvPolynomial (Fin (n + 1)) K |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i ∈ Ideal.span {ℓ}})
    (k : ℕ) (hk : m ≤ k) (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous k)
    (h : ℓ * f ∈ Ideal.span (Set.range F)) : f ∈ Ideal.span (Set.range F) :=
  P2MW.S_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span.solution n m g K F hF ℓ hℓ hcol hrel k hk f hf h
