/-
Ported from `Theorems/Thm_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isIso_of_isPullback_of_flat_of_surjective
    {S S' A B A' B' : Scheme.{uz}} (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    (pA : A ⟶ S) (pB : B ⟶ S) (φ : A ⟶ B) (hφ : φ ≫ pB = pA)
    (pA' : A' ⟶ S') (pB' : B' ⟶ S') (φ' : A' ⟶ B') (hφ' : φ' ≫ pB' = pA')
    (gA : A' ⟶ A) (gB : B' ⟶ B) (sqA : IsPullback gA pA' pA b) (sqB : IsPullback gB pB' pB b)
    (comm : φ' ≫ gB = gA ≫ φ) (hiso : IsIso φ') :
    IsIso φ :=
  P2MW.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective.solution b pA pB φ hφ pA' pB' φ' hφ' gA gB sqA sqB comm hiso
