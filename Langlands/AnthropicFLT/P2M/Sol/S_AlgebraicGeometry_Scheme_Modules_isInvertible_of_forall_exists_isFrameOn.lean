/-
Ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom
import Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    (h : ∀ x : X, ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ AlgebraicGeometry.Scheme.Modules.IsFrameOn s U) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, s, hx, hs⟩ := h x
  exact ⟨U, hx, AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit hs U le_rfl le_rfl⟩
