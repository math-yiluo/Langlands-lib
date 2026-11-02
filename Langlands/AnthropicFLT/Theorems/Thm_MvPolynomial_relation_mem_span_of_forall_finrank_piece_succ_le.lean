/-
Ported from `Theorems/Thm_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.relation_mem_span_of_forall_finrank_piece_succ_le
    (n m g : ℕ) (K : Type uz) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m)
    (hmax : ∀ J' : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J' = Ideal.span s) →
      Module.finrank K (piece J' m) = Module.finrank K (piece (Ideal.span (Set.range F)) m) →
      Module.finrank K (piece J' (m + 1)) ≤ Module.finrank K (piece (Ideal.span (Set.range F)) (m + 1)))
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) :
    c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K |
        (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0} :=
  P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.solution n m g K F hF hmax d c hc hcF
