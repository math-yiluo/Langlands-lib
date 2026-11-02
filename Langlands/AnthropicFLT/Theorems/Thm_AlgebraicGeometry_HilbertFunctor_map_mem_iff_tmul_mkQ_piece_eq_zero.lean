/-
Ported from `Theorems/Thm_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
open MvPolynomial TensorProduct AlgebraicGeometry.HilbertFunctor

theorem AlgebraicGeometry.HilbertFunctor.map_mem_iff_tmul_mkQ_piece_eq_zero
    (n : ℕ) (h : ℕ → ℕ) (B A : Type uz) [CommRing B] [CommRing A] (φ : B →+* A)
    (P : Point B n h) (Q : Point A n h) (hQ : Q.I = Ideal.map (MvPolynomial.map φ) P.I)
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) B) (hF : F.IsHomogeneous d) :
    MvPolynomial.map φ F ∈ Q.I ↔
      (letI : Algebra B A := φ.toAlgebra
       ((1 : A) ⊗ₜ[B] (Submodule.Quotient.mk ⟨F, (mem_homogeneousSubmodule d F).mpr hF⟩ : piece P.I d) :
          A ⊗[B] piece P.I d) = 0) :=
  P2MW.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero.solution n h B A φ P Q hQ d F hF
