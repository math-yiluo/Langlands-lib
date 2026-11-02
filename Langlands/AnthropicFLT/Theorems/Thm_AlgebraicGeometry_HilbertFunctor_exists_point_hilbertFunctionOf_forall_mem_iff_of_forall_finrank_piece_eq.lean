/-
Ported from `Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq
    (n : ℕ) (k : Type uz) [Field k] (P : Polynomial ℚ) (m : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (hP : ∀ d : ℕ, m ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ q : Point k n (hilbertFunctionOf n P m),
      ∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k), F.IsHomogeneous d → (F ∈ q.I ↔ F ∈ I) :=
  P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq.solution n k P m I hI hP
