/-
Ported from `Theorems/Thm_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open MvPolynomial hiding finrank_piece_succ_le_macaulayPow exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow finrank_piece_eq_of_maximal_growth finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow open AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
    (n m : ℕ) (hm : 1 ≤ m) (K : Type uz) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∀ e : ℕ, m ≤ e → Module.finrank K (piece J (e + 1)) = Nat.macaulayPow e (Module.finrank K (piece J e)) :=
  P2MW.S_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow.solution n m hm K J hJ hmax
