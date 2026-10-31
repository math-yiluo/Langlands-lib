/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.bijective_smul_unit_app_of_bijective_smul
    {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (σ : Γ(M, ⊤)) {V : X.Opens}
    (hσ : ∀ W : X.Opens, W ≤ V →
      Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : Γ(M, W)))
    (W' : X'.Opens) (hW' : W' ≤ p ⁻¹ᵁ V) :
    Function.Bijective fun g : Γ(X', W') =>
      g • (((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op
        ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) σ) :
          Γ((Scheme.Modules.pullback p).obj M, W')) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.solution X X' p M σ V hσ W' hW'
