/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
public import WeilConjectures.AlgebraicGeometry.ConstantModuleSheavesForgetColimits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.CategoryTheory.Sites.Adjunction

/-! # Canonical comparisons for forgetting module coefficients

The coefficient functor and its inverse-image comparison are independent of derived direct images.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The existing coefficientwise forgetful sheaf functor, abbreviated for comparisons. -/
abbrev moduleAbelianForget (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

instance moduleAbelianForget_additive (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (moduleAbelianForget Λ X).Additive where
  map_add := by intro F G α β; ext W; rfl

instance moduleAbelianForget_preservesFiniteLimits
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (moduleAbelianForget Λ X) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : U.IsRightAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom Λ) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsRightAdjoint
    have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom Λ)).isRightAdjoint
    infer_instance
  have : (moduleAbelianForget Λ X).IsRightAdjoint := by
    change (sheafCompose X.smallEtaleTopology U).IsRightAdjoint
    infer_instance
  infer_instance

instance moduleAbelianForget_preservesFiniteColimits
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (moduleAbelianForget Λ X) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1} (moduleAbelianForget Λ X) :=
    constantModuleSheaves_forget_preservesColimits X Λ
  infer_instance

/-- Inverse-image comparison adjoint to the forgotten module adjunction unit. -/
noncomputable def moduleAbelianUpperStarComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    moduleAbelianForget Λ Y ⋙ (g)^*[AddCommGrpCat.{u + 1}] ⟶
      (g)^*[ModuleCat.{u + 1} Λ] ⋙ moduleAbelianForget Λ X where
  app J := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
    ((moduleAbelianForget Λ Y).obj J)
    ((moduleAbelianForget Λ X).obj ((g)^*[ModuleCat.{u + 1} Λ].obj J))).symm
      ((moduleAbelianForget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app J))
  naturality {J K} h := by
    apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _ |>.injective
    dsimp only [Functor.comp_map]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Functor.comp_obj, Equiv.apply_symm_apply]
    change (moduleAbelianForget Λ Y).map h ≫
        (moduleAbelianForget Λ Y).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app K) =
      (moduleAbelianForget Λ Y).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app J) ≫
        (moduleAbelianForget Λ Y).map
          (((g)_*[ModuleCat.{u + 1} Λ]).map (((g)^*[ModuleCat.{u + 1} Λ]).map h))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (moduleAbelianForget Λ Y).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.naturality h)

/-- The canonical inverse-image comparison is invertible by the underived comparison. -/
instance moduleAbelianUpperStarComparison_isIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    IsIso (moduleAbelianUpperStarComparison Λ g) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro J
  exact isIso_moduleAbelianInverseImageComparison g Λ J

/-- The unit-compatible inverse-image coefficient isomorphism. -/
noncomputable def moduleAbelianUpperStarIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  asIso (moduleAbelianUpperStarComparison Λ g)

end AlgebraicGeometry.Etale
