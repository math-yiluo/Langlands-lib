/-
Ported from `Theorems/Thm_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

theorem AlgebraicGeometry.closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top
    {S : Scheme.{u}} [IsAffine S] {A B : CommRingCat.{u}} (a : Spec A ⟶ S) (b : Spec B ⟶ S) :
    Subring.closure
      (Set.range (pullback.fst a b).appTop ∪ Set.range (pullback.snd a b).appTop) = ⊤ :=
  P2MW.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top.solution a b
