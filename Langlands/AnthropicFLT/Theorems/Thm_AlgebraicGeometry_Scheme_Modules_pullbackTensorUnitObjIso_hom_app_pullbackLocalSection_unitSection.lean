/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom
import Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_PullbackMonoidal
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
    {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso φ).hom.app (φ ⁻¹ᵁ U)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ
        (AlgebraicGeometry.Scheme.Modules.unitSection U)) =
    AlgebraicGeometry.Scheme.Modules.unitSection (φ ⁻¹ᵁ U) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection.solution X Y φ U
