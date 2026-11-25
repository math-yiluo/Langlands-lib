/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower

/-!
# The first exterior power of a sheaf of modules

## References

* [Stacks: Tag 0BRT](https://stacks.math.columbia.edu/tag/0BRT)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

-- Naturality elaborates restrictions across the scheme and ring-sheaf module interfaces.
/-- The first exterior power `⋀¹ M` of a sheaf of modules `M` is isomorphic to `M`. -/
theorem exteriorSheaf_one_iso {X : Scheme.{u}} (M : X.Modules) :
    Nonempty (exteriorPower M 1 ≅ M) := by
  let e : (_root_.PresheafOfModules.exteriorPower (R := _) M.val 1) ≅ M.val :=
    PresheafOfModules.isoMk
      (fun U ↦ (exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)).toModuleIso)
      (by
        intro U V f
        ext x
        obtain ⟨m, rfl⟩ :=
          (exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)).symm.surjective x
        change exteriorPower.oneEquiv (X.presheaf.obj V) (M.val.obj V)
            (((_root_.PresheafOfModules.exteriorPower (R := _) M.val 1).map f)
              ((exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)).symm m)) =
          M.val.map f
            (exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)
              ((exteriorPower.oneEquiv (X.presheaf.obj U) (M.val.obj U)).symm m))
        rw [LinearEquiv.apply_symm_apply, exteriorPower.oneEquiv_symm_apply]
        have h := (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := _) M.val 1 f) (fun _ ↦ m)
        exact (congrArg (exteriorPower.oneEquiv (X.presheaf.obj V) (M.val.obj V)) h).trans
          (exteriorPower.oneEquiv_ιMulti _))
  exact ⟨(PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso e ≪≫
    asIso (C := SheafOfModules.{u} X.ringCatSheaf)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app M)⟩

end AlgebraicGeometry.Scheme.Modules
