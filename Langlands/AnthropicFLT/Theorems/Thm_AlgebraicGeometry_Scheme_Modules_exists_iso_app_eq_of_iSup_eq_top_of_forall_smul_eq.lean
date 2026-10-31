/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
    {X : Scheme.{u}} {ι : Type u} [LinearOrder ι] (T : ι → X.Opens) (hT : ⨆ k, T k = ⊤)
    {L L' : X.Modules} (s : ∀ k, Γ(L, T k)) (s' : ∀ k, Γ(L', T k))
    (hs : ∀ k, Scheme.Modules.IsFrameOn (s k) (T k)) (hs' : ∀ k, Scheme.Modules.IsFrameOn (s' k) (T k))
    (h : ∀ (i j : ι), i < j → ∀ g : Γ(X, T i ⊓ T j),
      HSMul.hSMul g (L.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s i)) =
          L.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s j) →
        HSMul.hSMul g (L'.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s' i)) =
          L'.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s' j)) :
    ∃ e : L ≅ L', ∀ k, e.hom.app (T k) (s k) = s' k := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq.solution X ι _ T hT L L' s s' hs hs' h
