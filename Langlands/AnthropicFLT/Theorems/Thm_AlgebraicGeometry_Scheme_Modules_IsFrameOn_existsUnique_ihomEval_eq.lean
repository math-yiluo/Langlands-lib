/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.existsUnique_ihomEval_eq
    {X : Scheme.{u}} {P Q : X.Modules} {V : X.Opens} {p : Γ(P, V)}
    (hp : Scheme.Modules.IsFrameOn p V) (q : Γ(Q, V)) :
    ∃! θ : Γ((ihom P).obj Q, V), Scheme.Modules.ihomEval P Q V p θ = q := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq.solution X P Q V p hp q
