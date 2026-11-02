/-
Ported from `Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map
    (n : ℕ) (A B : Type uz) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    (∀ q ∈ I.map (MvPolynomial.map (algebraMap A B)), ∀ d : ℕ,
        homogeneousComponent d q ∈ I.map (MvPolynomial.map (algebraMap A B))) ∧
    ∀ d : ℕ, ∃ e : B ⊗[A] piece I d ≃ₗ[B] piece (I.map (MvPolynomial.map (algebraMap A B))) d,
      ∀ (p : MvPolynomial (Fin (n + 1)) A) (hp : p.IsHomogeneous d),
        e (1 ⊗ₜ[A] Submodule.Quotient.mk ⟨p, hp⟩) =
          Submodule.Quotient.mk ⟨MvPolynomial.map (algebraMap A B) p, hp.map (algebraMap A B)⟩ :=
  P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.solution n A B I hI
