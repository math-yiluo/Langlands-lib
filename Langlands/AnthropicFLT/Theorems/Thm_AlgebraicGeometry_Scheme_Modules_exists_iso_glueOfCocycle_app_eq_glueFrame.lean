/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c : Scheme.Modules.UnitCocycle U)
    {M : X.Modules} (e : ∀ i, Γ(M, U i)) (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (U i))
    (htrans : ∀ i j, M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i)) :
    ∃ φ : M ≅ Scheme.Modules.glueOfCocycle c, ∀ i, φ.hom.app (U i) (e i) = Scheme.Modules.glueFrame c i := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame.solution X ι U hU c M e he htrans
