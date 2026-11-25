/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Coherence of restriction and pullback for successive coefficient maps

## References

* Stacks Project, Tags 03EL, 03DA and 06YY
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry.Scheme

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso
  comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryNatIso
  proEtaleRingModulePullback proEtaleRingModuleAdjunction

private theorem restrictionComp_inv_sections
    (T : Scheme.{u}) {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (N : reductionModules T B) (U : T.ProEtᵒᵖ) (x : N.val.obj U) :
    ((pbcRestrictComp a b c h).inv.app N).val.app U x = x := by
  have hh := (pbcRestrictComp_exists a b c h).exists.choose_spec N U
  calc
    _ = ((pbcRestrictComp a b c h).hom.app N).val.app U
        (((pbcRestrictComp a b c h).inv.app N).val.app U x) := (hh _).symm
    _ = x := by
      have he := congrArg (fun z ↦ z.val.app U)
        ((pbcRestrictComp a b c h).inv_hom_id_app N)
      exact ConcreteCategory.congr_hom he
        (show ((pbcRestrict c).obj N).val.obj U from x)

private theorem mate_naturality
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R')
    {G G' : C ⥤ E} {H H' : D ⥤ F}
    (μ : TwoSquare G L L' H) (ν : TwoSquare G' L L' H')
    (p : G ⟶ G') (q : H ⟶ H')
    (h : ∀ N, p.app (R.obj N) ≫ (mateEquiv a b ν).app N =
      (mateEquiv a b μ).app N ≫ R'.map (q.app N)) (M : C) :
    L'.map (p.app M) ≫ ν.app M = μ.app M ≫ q.app (L.obj M) := by
  change G ⋙ L' ⟶ L ⋙ H at μ
  change G' ⋙ L' ⟶ L ⋙ H' at ν
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := b.unit.naturality (p.app M)
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [← reassoc_of% hu]
  have hν := unit_mateEquiv a b ν M
  have hμ := unit_mateEquiv a b μ M
  dsimp only [Functor.id_obj] at hν hμ
  rw [← hν, ← reassoc_of% hμ]
  rw [← p.naturality_assoc]
  exact congrArg (fun z ↦ G.map (a.unit.app M) ≫ z) (h (L.obj M))

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
    (RX SX TX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY SY TY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (aX : RX ⟶ SX) (bX : SX ⟶ TX) (cX : RX ⟶ TX) (hX : aX ≫ bX = cX)
    (aY : RY ⟶ SY) (bY : SY ⟶ TY) (cY : RY ⟶ TY) (hY : aY ≫ bY = cY)
    (eR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RX ≅ RY)
    (eS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SX ≅ SY)
    (eT : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj TX ≅ TY)
    (ha : eR.hom ≫ aY =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aX ≫ eS.hom)
    (hb : eS.hom ≫ bY =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map bX ≫ eT.hom)
    (hc : eR.hom ≫ cY =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map cX ≫ eT.hom)

/-- Pullback commutes coherently with successive exact scalar restrictions. -/
theorem proEtaleRestrictionPullback_scalarComposition
    (M : reductionDerivedCategory X TX) :
    (proEtaleRingRestrictionDerivedPullback f RX TX RY TY cX cY eR eT hc).inv.app M ≫
        (pbcDerivedRestrictComp aY bY cY hY).inv.app
          ((proEtaleRingDerivedPullback f TX TY eT).obj M) =
      (proEtaleRingDerivedPullback f RX RY eR).map
          ((pbcDerivedRestrictComp aX bX cX hX).inv.app M) ≫
        (proEtaleRingRestrictionDerivedPullback f RX SX RY SY aX aY eR eS ha).inv.app
          ((reductionDerivedRestrict X bX).obj M) ≫
        (reductionDerivedRestrict Y aY).map
          ((proEtaleRingRestrictionDerivedPullback f SX TX SY TY bX bY eS eT hb).inv.app M) := by
  let LR := proEtaleRingModulePullback f RX RY eR
  let LS := proEtaleRingModulePullback f SX SY eS
  let LT := proEtaleRingModulePullback f TX TY eT
  let ar := proEtaleRingModuleAdjunction f RX RY eR
  let as_ := proEtaleRingModuleAdjunction f SX SY eS
  let at_ := proEtaleRingModuleAdjunction f TX TY eT
  let ηX := pbcRestrictComp aX bX cX hX
  let ηY := pbcRestrictComp aY bY cY hY
  let da := proEtaleRingRestrictionDirectImage f RX SX RY SY aX aY eR eS ha
  let db := proEtaleRingRestrictionDirectImage f SX TX SY TY bX bY eS eT hb
  let dc := proEtaleRingRestrictionDirectImage f RX TX RY TY cX cY eR eT hc
  let α := TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionPullbackInv f RX SX RY SY aX aY eR eS ha)
  let β := TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionPullbackInv f SX TX SY TY bX bY eS eT hb)
  let γ := TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionPullbackInv f RX TX RY TY cX cY eR eT hc)
  have hma : mateEquiv as_ ar α = TwoSquare.mk _ _ _ _ da.hom :=
    restrictionPullback_mate f RX SX RY SY aX aY eR eS ha
  have hmb : mateEquiv at_ as_ β = TwoSquare.mk _ _ _ _ db.hom :=
    restrictionPullback_mate f SX TX SY TY bX bY eS eT hb
  have hmc : mateEquiv at_ ar γ = TwoSquare.mk _ _ _ _ dc.hom :=
    restrictionPullback_mate f RX TX RY TY cX cY eR eT hc
  have hm := mateEquiv_vcomp at_ as_ ar β α
  rw [hma, hmb] at hm
  have hd (N : proEtaleRingModules Y TY) :
      ηX.inv.app ((proEtaleRingModuleDirectImage f TX TY eT).obj N) ≫
          (proEtaleRingRestrictScalars aX).map (db.hom.app N) ≫
          da.hom.app ((proEtaleRingRestrictScalars bY).obj N) =
        dc.hom.app N ≫
          (proEtaleRingModuleDirectImage f RX RY eR).map (ηY.inv.app N) := by
    ext U x
    change ((da.hom.app ((proEtaleRingRestrictScalars bY).obj N)).val.app U)
      ((db.hom.app N).val.app U
        ((ηX.inv.app ((proEtaleRingModuleDirectImage f TX TY eT).obj N)).val.app U x)) =
      (ηY.inv.app N).val.app ((proEtaleBaseChange f).op.obj U)
        ((dc.hom.app N).val.app U x)
    dsimp only [da, db, dc, ηX, ηY, proEtaleRingRestrictionDirectImage]
    erw [(proEtaleRingRestrictionDirectImage_existsUnique
        f SX TX SY TY bX bY eS eT hb).choose_spec.1,
      (proEtaleRingRestrictionDirectImage_existsUnique
        f RX SX RY SY aX aY eR eS ha).choose_spec.1,
      (proEtaleRingRestrictionDirectImage_existsUnique
        f RX TX RY TY cX cY eR eT hc).choose_spec.1,
      restrictionComp_inv_sections, restrictionComp_inv_sections]
  have hq (N : proEtaleRingModules X TX) :
      LR.map (ηX.inv.app N) ≫ α.app ((proEtaleRingRestrictScalars bX).obj N) ≫
          (proEtaleRingRestrictScalars aY).map (β.app N) =
        γ.app N ≫ ηY.inv.app (LT.obj N) := by
    have hp : LR.map (ηX.inv.app N) ≫ (β ≫ₕ α).app N =
        γ.app N ≫ ηY.inv.app (LT.obj N) := by
      apply mate_naturality at_ ar γ (β ≫ₕ α) ηX.inv ηY.inv (fun P ↦ ?_) N
      rw [hm, hmc]
      simpa only [TwoSquare.vComp, TwoSquare.mk, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
        using hd P
    simpa only [TwoSquare.hComp, TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
      using hp
  have hder := Functor.exactSquare_comp_forward
    (proEtaleRingRestrictScalars bX) (proEtaleRingRestrictScalars aX)
    (proEtaleRingRestrictScalars cX)
    (proEtaleRingRestrictScalars bY) (proEtaleRingRestrictScalars aY)
    (proEtaleRingRestrictScalars cY) LT LS LR
    (asIso β) (asIso α) (asIso γ)
    ηX.symm ηY.symm hq M
  have hα :
      (proEtaleRingRestrictionDerivedPullback f RX SX RY SY aX aY eR eS ha).inv =
        (Functor.mapDerivedCategorySquareIso (asIso α)).hom := by
    change (Functor.mapDerivedCategorySquareIso (asIso α).symm).inv = _
    simpa only [Iso.symm_symm_eq] using
      (Functor.square_symm_hom (asIso α).symm).symm
  have hβ :
      (proEtaleRingRestrictionDerivedPullback f SX TX SY TY bX bY eS eT hb).inv =
        (Functor.mapDerivedCategorySquareIso (asIso β)).hom := by
    change (Functor.mapDerivedCategorySquareIso (asIso β).symm).inv = _
    simpa only [Iso.symm_symm_eq] using
      (Functor.square_symm_hom (asIso β).symm).symm
  have hγ :
      (proEtaleRingRestrictionDerivedPullback f RX TX RY TY cX cY eR eT hc).inv =
        (Functor.mapDerivedCategorySquareIso (asIso γ)).hom := by
    change (Functor.mapDerivedCategorySquareIso (asIso γ).symm).inv = _
    simpa only [Iso.symm_symm_eq] using
      (Functor.square_symm_hom (asIso γ).symm).symm
  simpa only [hα, hβ, hγ, pbcDerivedRestrictComp, pbcDerivedRestrict,
    reductionDerivedRestrict, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc, LT, LS, LR, ηX, ηY,
    proEtaleRingDerivedPullback, pbcRestrict, reductionRestrict,
    proEtaleRingRestrictScalars] using hder.symm

end AlgebraicGeometry.Scheme
