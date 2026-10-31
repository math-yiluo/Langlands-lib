/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    {B : Type v} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1) :
    ∃ φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B,
      ∀ k, φ (ProjSpace.ratio R n i k) = b k :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.solution R n i b hb
