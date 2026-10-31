/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.isInvertible_glueOfCocycle
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c : Scheme.Modules.UnitCocycle U) :
    Scheme.Modules.IsInvertible (Scheme.Modules.glueOfCocycle c) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle.solution X ι U hU c
