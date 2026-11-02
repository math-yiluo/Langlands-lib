/-
Ported from `Definitions/Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports. The paired Markdown file lists
the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)

@[reducible] def moduleRestrict {U U' : V.Opens} (h : U ≤ U') : Module Γ(V, U') (F.obj U) :=
  Module.compHom (F.obj U) (V.presheaf.map (homOfLE h).op).hom

def resₗ {U U' : V.Opens} (h : U ≤ U') :
    letI := F.moduleRestrict h
    F.obj U' →ₗ[Γ(V, U')] F.obj U :=
  letI := F.moduleRestrict h
  { toFun := F.res h
    map_add' := map_add _
    map_smul' := fun a x => F.res_smul h a x }

theorem resₗ_apply {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') :
    letI := F.moduleRestrict h
    F.resₗ h x = F.res h x := rfl

theorem moduleRestrict_smul_def {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U')) (x : F.obj U) :
    letI := F.moduleRestrict h
    a • x = (V.presheaf.map (homOfLE h).op).hom a • x := rfl

end AlgebraicGeometry.OModulePresheaf

end
