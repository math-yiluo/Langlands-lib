/-
Ported from `Theorems/Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField
    {X Y : Scheme.{u}} (q : X ⟶ Y) [QuasiCompact q] [QuasiSeparated q]
    {K : Type u} [Field K] (k : Spec (CommRingCat.of K) ⟶ Y)
    (h : Function.Bijective (q.fiberToSpecResidueField (k.base (IsLocalRing.closedPoint K))).appTop) :
    Function.Bijective (pullback.snd q k).appTop :=
  P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.solution q k h
