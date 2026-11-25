/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding

/-!
# Compatibility of the two canonical finite-coefficient realizations

## References

* Stacks Project, Modules on Sites, Tag 03EI
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

private noncomputable def realizationRestrictionUnit
    (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (M : Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    M ⟶ (Scheme.proEtaleModuleRestriction T B).obj
      ((finiteCoefficientIntrinsicRealization T B).obj M) := by
  let P := (finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} B)).obj M.obj
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (finiteCoefficientIntrinsicScalarMap T B)).unit.app P
  exact ⟨{ app := η.app
           naturality := fun _ _ f ↦ by
             ext x
             exact ConcreteCategory.congr_hom (η.naturality f) x }⟩

private theorem realizationRestrictionUnit_isIso
    (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (M : Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    IsIso (realizationRestrictionUnit T B M) := by
  rw [← isIso_iff_of_reflects_iso _
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1}))]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  change IsIso (toSheafify (Scheme.ProEt.topology T)
    (M.obj ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1}))
  exact isIso_toSheafify (Scheme.ProEt.topology T)
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1})).obj M).property

/-- Restricting the canonical associated module sheaf recovers the original module sheaf. -/
theorem intrinsicRealization_restriction
    (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B] :
    Nonempty (finiteCoefficientIntrinsicRealization T B ⋙
      Scheme.proEtaleModuleRestriction T B ≅ 𝟭 _) := by
  refine ⟨(NatIso.ofComponents (fun M ↦ ?_) ?_).symm⟩
  · have := realizationRestrictionUnit_isIso T B M
    exact asIso (realizationRestrictionUnit T B M)
  · intro M N f
    ext U x
    exact ConcreteCategory.congr_hom
      (congrArg (fun z ↦ z.app U)
        ((PresheafOfModules.sheafificationAdjunction.{u + 1}
          (finiteCoefficientIntrinsicScalarMap T B)).unit.naturality
            ((finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} B)).map f.hom))) x

end AlgebraicGeometry.ProEtale
