/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules) (hM : IsIso M.fromTildeΓ) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv
        ((moduleSpecΓFunctor (R := R)).obj M)
        ((moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj M))).symm
      ((moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
        (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((Scheme.Modules.pullback (Spec.map φ)).obj M))) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.solution R S φ M hM
