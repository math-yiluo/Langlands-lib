/-
Ported from `Theorems/Thm_MvPolynomial_finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt
    (n m : ℕ) (hm : 1 ≤ m) (k : Type uz) [Field k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) k), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (a : Fin (n + 1) → k)
    (hgrowth : Module.finrank k (piece (J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)}) (m + 1)) =
      Nat.macaulayPow m (Module.finrank k (piece (J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)}) m)))
    (hsum : Nat.macaulayPow m (Module.finrank k (piece (J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)}) m)) +
        Module.finrank k (piece J m) = Nat.macaulayPow m (Module.finrank k (piece J m))) :
    let J' : Ideal (MvPolynomial (Fin (n + 1)) k) :=
      Ideal.span {f | f ∈ J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)} ∧ f.IsHomogeneous m}
    Module.finrank k (piece J' (m + 1)) = Nat.macaulayPow m (Module.finrank k (piece J' m)) ∧
    (0 < Module.finrank k (piece J m) → Module.finrank k (piece J' m) < Module.finrank k (piece J m)) :=
  P2MW.S_MvPolynomial_finrank_piece_span_sup_linearForm_eq_macaulayPow_and_lt.solution n m hm k J hJ a hgrowth hsum
