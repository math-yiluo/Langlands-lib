/-
Ported from `Theorems/Thm_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem MvPolynomial.finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp
    (n : ℕ) (K : Type uz) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcolon : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d → ℓ * F ∈ J → F ∈ J)
    (d : ℕ) :
    Module.finrank K (piece (J ⊔ Ideal.span {ℓ}) (d + 1)) + Module.finrank K (piece J d) =
      Module.finrank K (piece J (d + 1)) :=
  P2MW.S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.solution n K J hJ ℓ hℓ hcolon d
