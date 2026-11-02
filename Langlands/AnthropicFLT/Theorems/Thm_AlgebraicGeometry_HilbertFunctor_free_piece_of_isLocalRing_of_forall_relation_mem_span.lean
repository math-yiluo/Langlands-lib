/-
Ported from `Theorems/Thm_AlgebraicGeometry_HilbertFunctor_free_piece_of_isLocalRing_of_forall_relation_mem_span.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_free_piece_of_isLocalRing_of_forall_relation_mem_span
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem AlgebraicGeometry.HilbertFunctor.free_piece_of_isLocalRing_of_forall_relation_mem_span
    (n m g : ℕ) (A : Type uz) [CommRing A] [IsLocalRing A]
    (F : Fin g → MvPolynomial (Fin (n + 1)) A) (hF : ∀ i, (F i).IsHomogeneous m)
    (h₀ : Module.Projective A (piece (Ideal.span (Set.range F)) m))
    (h₁ : Module.Projective A (piece (Ideal.span (Set.range F)) (m + 1)))
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A)),
      (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * MvPolynomial.map (IsLocalRing.residue A) (F i) = 0 →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A))
        {l : Fin g → MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A) |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧
          ∑ i, l i * MvPolynomial.map (IsLocalRing.residue A) (F i) = 0}) :
    ∀ e, Module.Free A (piece (Ideal.span (Set.range F)) e) :=
  P2MW.S_AlgebraicGeometry_HilbertFunctor_free_piece_of_isLocalRing_of_forall_relation_mem_span.solution n m g A F hF h₀ h₁ hrel
