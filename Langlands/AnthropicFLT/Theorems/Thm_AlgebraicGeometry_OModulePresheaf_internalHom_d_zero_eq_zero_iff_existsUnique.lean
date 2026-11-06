/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.internalHom_d_zero_eq_zero_iff_existsUnique
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
    (hGq : G.IsQuasicoherent) (K : V.OrderedAffineCover) (c : (OModulePresheaf.internalHom F G).cochain K 0) :
    (OModulePresheaf.internalHom F G).d K 0 c = 0 ↔
      ∃! φ : (OModulePresheaf.internalHom F G).obj ⊤,
        ∀ s : K.Idx 0, c s = (OModulePresheaf.internalHom F G).res le_top φ :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.solution hGq K c
