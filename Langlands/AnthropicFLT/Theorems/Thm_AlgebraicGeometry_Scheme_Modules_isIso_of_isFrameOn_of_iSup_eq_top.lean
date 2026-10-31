/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top
    {X : Scheme.{u}} {P Q : X.Modules} (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, Scheme.Modules.IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, Scheme.Modules.IsFrameOn (q i) (𝒱 i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top.solution X P Q μ ι 𝒱 hcov p q hp hq hμ
