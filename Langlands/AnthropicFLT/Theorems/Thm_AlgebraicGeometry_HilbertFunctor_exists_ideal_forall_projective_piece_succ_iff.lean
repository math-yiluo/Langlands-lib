/-
Ported from `Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_projective_piece_succ_iff.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_projective_piece_succ_iff
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem AlgebraicGeometry.HilbertFunctor.exists_ideal_forall_projective_piece_succ_iff
    (n m q r : ℕ)
    (hmax : ∀ (K : Type uz) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s) →
      Module.finrank K (piece J m) = q → Module.finrank K (piece J (m + 1)) ≤ r)
    (A : Type uz) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∃ s : Set (MvPolynomial (Fin (n + 1)) A), (∀ p ∈ s, p.IsHomogeneous m) ∧ I = Ideal.span s)
    (hproj : Module.Projective A (piece I m))
    (hrank : ∀ p : PrimeSpectrum A, Module.rankAtStalk (piece I m) p = q) :
    ∃ 𝔞 : Ideal A, ∀ (B : Type uz) [CommRing B] [Algebra A B],
      (Module.Projective B (piece (I.map (MvPolynomial.map (algebraMap A B))) (m + 1)) ∧
        ∀ 𝔮 : PrimeSpectrum B,
          Module.rankAtStalk (piece (I.map (MvPolynomial.map (algebraMap A B))) (m + 1)) 𝔮 = r) ↔
      ∀ a ∈ 𝔞, algebraMap A B a = 0 :=
  P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_projective_piece_succ_iff.solution n m q r hmax A I hI hproj hrank
