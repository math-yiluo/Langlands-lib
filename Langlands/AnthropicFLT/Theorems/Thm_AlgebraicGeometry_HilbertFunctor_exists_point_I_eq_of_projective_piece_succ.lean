/-
Ported from `Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_of_projective_piece_succ.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_of_projective_piece_succ
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_of_projective_piece_succ
    (n m : ℕ) (h : ℕ → ℕ) (h₁ : ∀ d, d < m → h d = Nat.choose (n + d) n)
    (h₂ : ∀ e, m ≤ e → ∀ (K : Type uz) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
    (h₃ : ∀ e, m ≤ e → ∃ (K : Type uz) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = h e ∧ Module.finrank K (piece J (e + 1)) = h (e + 1))
    (A : Type uz) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∃ s : Set (MvPolynomial (Fin (n + 1)) A), (∀ p ∈ s, p.IsHomogeneous m) ∧ I = Ideal.span s)
    (hm : Module.Projective A (piece I m) ∧
      ∀ p : PrimeSpectrum A, Module.rankAtStalk (piece I m) p = h m)
    (hm₁ : Module.Projective A (piece I (m + 1)) ∧
      ∀ p : PrimeSpectrum A, Module.rankAtStalk (piece I (m + 1)) p = h (m + 1)) :
    ∃ P : Point A n h, P.I = I :=
  P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_of_projective_piece_succ.solution n m h h₁ h₂ h₃ A I hI hm hm₁
