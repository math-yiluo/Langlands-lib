/-
Ported from `Theorems/Thm_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.HilbertFunctor open _root_.MvPolynomial hiding finrank_piece_succ_le_macaulayPow
attribute [local instance] MvPolynomial.gradedAlgebra

theorem MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq
    (n g : ℕ) (hg : 1 ≤ g) (H : ℕ → ℕ)
    (hH : ∀ e : ℕ, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (K : Type uz) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (hev : ∃ D : ℕ, ∀ e : ℕ, D ≤ e → Module.finrank K (piece J e) = H e) :
    ∀ d : ℕ, g ≤ d → H d ≤ Module.finrank K (piece J d) :=
  P2MW.S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq.solution n g hg H hH K J hJ hev
