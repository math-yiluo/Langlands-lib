/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback
    {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (m : Γ(M, ⊤)) (z : X')
    (h : ∃ U' : X'.Opens, z ∈ U' ∧ ∀ V' : X'.Opens, V' ≤ U' →
      Function.Bijective fun g : Γ(X', V') =>
        g • (((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) m) :
            Γ((Scheme.Modules.pullback p).obj M, V'))) :
    ∃ U : X.Opens, p z ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(M, V)) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.solution X X' p M hM m z h
