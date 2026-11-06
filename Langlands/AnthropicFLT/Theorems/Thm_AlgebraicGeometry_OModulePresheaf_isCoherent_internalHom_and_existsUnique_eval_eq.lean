/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) [IsLocallyNoetherian V]
    (F G : OModulePresheaf π)
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent) :
    (internalHom F G).IsCoherent ∧ (internalHom F G).IsQuasicoherent ∧
      ∀ (U : V.affineOpens) (f : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1),
        ∃! φ : (internalHom F G).obj U.1, ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = f x :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq.solution π F G hFc hFq hGc hGq
