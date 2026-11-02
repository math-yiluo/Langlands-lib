/-
Ported from `Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_map
    (n : ℕ) (h : ℕ → ℕ) (A B : Type uz) [CommRing A] [CommRing B] [Algebra A B] (P : Point A n h) :
    ∃ Q : Point B n h, Q.I = P.I.map (MvPolynomial.map (algebraMap A B)) :=
  P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map.solution n h A B P
