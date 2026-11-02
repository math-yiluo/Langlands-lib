/-
Ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection_monoidalV2.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped and its commands are replaced
by standard Lean commands. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom
import Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection_monoidalV2

universe u

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

set_option autoImplicit false

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} {U V : X.Opens} {s : Γ(L, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n) V := by
  induction n with
  | zero => exact AlgebraicGeometry.Scheme.Modules.isFrameOn_unitSection V
  | succ n ih =>
    rw [AlgebraicGeometry.Scheme.Modules.tensorPowSection_succ]
    exact AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections_monoidalV2 ih hs
