/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory

/-! # First-projection supported source normalization
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar

/-- The normalized ordinary supported-source inverse is the canonical direct-image composite. -/
theorem ordinary_source_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (e : Mod.regular (condensedRingObj Λ (ProjectiveLine Y)) ≅
      (CondensedRing.lowerStar Λ f).obj (source Λ Y))
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (hn : SupportNormalization Λ Y f e h) :
    e.inv = (CondensedRing.lowerStarComp Λ (diagonalImmersion Y) f ≪≫
      CondensedRing.lowerStarCongr Λ h ≪≫
        CondensedRing.lowerStarId Λ (ProjectiveLine Y)).hom.app
          (Mod.regular (condensedRingObj Λ (ProjectiveLine Y))) := by
  apply Mod.hom_ext
  unfold SupportNormalization at hn
  apply eq_of_heq
  rw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app,
    Mod.comp_hom', Mod.comp_hom', CondensedRing.lowerStarComp_hom_app_hom,
    CondensedRing.lowerStarCongr_hom_app_hom, CondensedRing.lowerStarId_hom_app_hom]
  simp only [Iso.trans_hom, NatTrans.comp_app, CondensedRing.lowerStar_obj_X] at hn ⊢
  exact hn
end AlgebraicGeometry.ProEtale.RationalP1
