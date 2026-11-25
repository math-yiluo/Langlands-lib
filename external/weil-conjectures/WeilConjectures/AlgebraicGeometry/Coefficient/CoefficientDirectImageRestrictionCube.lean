/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientEquivalence
public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateThickLocus

/-! # The ordinary coefficient restriction cube
Source: Stacks Project, Cohomology on Sites, Tags 0D6E and 07A6.
(blueprint: lem-pbc-coefficient-direct-image-restriction-cube).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem restrictionComp_apply {T : Scheme.{u}}
    {A B C : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c)
    (M : pbcModules T C) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp a b c h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists a b c h).exists.choose_spec M U x

private theorem restrictionComp_inv_apply {T : Scheme.{u}}
    {A B C : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c)
    (M : pbcModules T C) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp a b c h).inv.app M).val.app U x = x := by
  have hh := congrArg (fun t ↦ t.val.app U x)
    ((pbcRestrictComp a b c h).inv_hom_id_app M)
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, restrictionComp_apply, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] using hh

private theorem coefficientComparison_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (RV SV : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
    (hc : cR.hom ≫ aU =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)
    (M : pbcModules X SU) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleBaseChange f).op.obj U)) :
    ((proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS hc).hom.app M).val.app
      U x = x :=
  (proEtaleRingRestrictionDirectImage_existsUnique
    f RV SV RU SU aV aU cR cS hc).choose_spec.1 M U x

attribute [local irreducible] proEtaleRingRestrictionDirectImage

/-- The ordinary coefficient comparisons satisfy the restriction cube on module sheaves.
Source: Stacks 0D6E and 07A6, ordinary direct image and restriction of coefficients.
(blueprint: lem-pbc-coefficient-direct-image-restriction-cube).

Proof: every restriction compositor and canonical direct-image coefficient comparison
is the identity on sections. The supplied comparison has the same property by `hi`;
its inverse does too, by cancellation. Expand composition and direct image on sections.
Both paths are the identity map, so sectionwise faithfulness proves the equality. -/
theorem coefficientDirectImageRestrictionCube
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R₀ R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (b : R₀ ≅ R)
    (SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (φY : R ⟶ SY) (φX : RX ⟶ SX)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ RX)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (hc : cR.hom ≫ φX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map φY ≫ cS.hom)
    (i : pbcRestrict φX ⋙ proEtaleRingModuleDirectImage f R RX cR ≅
      proEtaleRingModuleDirectImage f SY SX cS ⋙ pbcRestrict φY)
    (hi : ∀ (M : pbcModules X SX) (U : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (i.hom.app M).val.app U x)
        (fun x : ((proEtaleRingModuleDirectImage f SY SX cS).obj M).val.obj U ↦ x)) :
  let χ := b.hom ≫ φY
  let q := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso b ≪≫ cR
  let hq : q.hom ≫ φX = DerivedScalarMate.inverseMap f χ ≫ cS.hom := by
    dsimp only [q, χ, Iso.trans_hom, Functor.mapIso_hom, DerivedScalarMate.inverseMap]
    rw [Category.assoc, hc, ← Category.assoc, ← Functor.map_comp]
  let H := proEtaleRingModuleDirectImage f R₀ (DerivedScalarMate.inverseRing f R₀)
    (Iso.refl _)
  let GS := proEtaleRingModuleDirectImage f SY SX cS
  let cp := proEtaleRingRestrictionDirectImage f R₀ R
    (DerivedScalarMate.inverseRing f R₀) RX b.hom q.hom (Iso.refl _) cR (by simp [q])
  let cz := proEtaleRingRestrictionDirectImage f SY SY
    (DerivedScalarMate.inverseRing f SY) SX (𝟙 SY) cS.hom (Iso.refl _) cS (by simp)
  let cd := proEtaleRingRestrictionDirectImage f R₀ SY
    (DerivedScalarMate.inverseRing f R₀) (DerivedScalarMate.inverseRing f SY)
    χ (DerivedScalarMate.inverseMap f χ) (Iso.refl _) (Iso.refl _) (by simp)
  let a := pbcRestrictComp q.hom φX (q.hom ≫ φX) rfl ≪≫
    (pbcRestrictComp (DerivedScalarMate.inverseMap f χ) cS.hom
      (q.hom ≫ φX) hq.symm).symm
  let d := pbcRestrictComp b.hom φY χ rfl ≪≫
    (pbcRestrictComp χ (𝟙 SY) χ (by simp)).symm
  ∀ M : pbcModules X SX,
      d.hom.app (GS.obj M) ≫ (pbcRestrict χ).map (cz.hom.app M) ≫
        cd.hom.app ((pbcRestrict cS.hom).obj M) =
      (pbcRestrict b.hom).map (i.inv.app M) ≫
        cp.hom.app ((pbcRestrict φX).obj M) ≫ H.map (a.hom.app M) := by
  intro χ q hq H GS cp cz cd a d
  let J := proEtaleRingModuleDirectImage f SY (DerivedScalarMate.inverseRing f SY)
    (Iso.refl _)
  let FR := proEtaleRingModuleDirectImage f R RX cR
  have hiApp (M : pbcModules X SX) (U : Y.ProEtᵒᵖ)
      (x : (GS.obj M).val.obj U) : (i.hom.app M).val.app U x = x := by
    exact congrFun (eq_of_heq (hi M U)) x
  have hiInv (M : pbcModules X SX) (U : Y.ProEtᵒᵖ)
      (x : (GS.obj M).val.obj U) : (i.inv.app M).val.app U x = x := by
    have h := congrArg (fun t ↦ t.val.app U x) (i.inv_hom_id_app M)
    simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, hiApp, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] using h
  have cpApp (M : pbcModules X RX) (U : Y.ProEtᵒᵖ)
      (x : (FR.obj M).val.obj U) : (cp.hom.app M).val.app U x = x := by
    exact coefficientComparison_apply f R₀ R
      (DerivedScalarMate.inverseRing f R₀) RX b.hom q.hom (Iso.refl _) cR
      (by simp [q]) M U x
  have czApp (M : pbcModules X SX) (U : Y.ProEtᵒᵖ)
      (x : (GS.obj M).val.obj U) : (cz.hom.app M).val.app U x = x := by
    exact coefficientComparison_apply f SY SY
      (DerivedScalarMate.inverseRing f SY) SX (𝟙 SY) cS.hom (Iso.refl _) cS
      (by simp) M U x
  have cdApp (M : pbcModules X (DerivedScalarMate.inverseRing f SY)) (U : Y.ProEtᵒᵖ)
      (x : (J.obj M).val.obj U) : (cd.hom.app M).val.app U x = x := by
    exact coefficientComparison_apply f R₀ SY
      (DerivedScalarMate.inverseRing f R₀) (DerivedScalarMate.inverseRing f SY)
      χ (DerivedScalarMate.inverseMap f χ) (Iso.refl _) (Iso.refl _)
      (by simp) M U x
  intro M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  have hd (x : ((pbcRestrict φY ⋙ pbcRestrict b.hom).obj (GS.obj M)).val.obj U) :
      (d.hom.app (GS.obj M)).val.app U x = x := by
    simp only [d, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      restrictionComp_apply, restrictionComp_inv_apply]
  have hcz (x : ((pbcRestrict χ).obj ((pbcRestrict (𝟙 SY)).obj (GS.obj M))).val.obj U) :
      ((pbcRestrict χ).map (cz.hom.app M)).val.app U x = x := by
    exact czApp M U x
  have hi (x : ((pbcRestrict b.hom).obj ((pbcRestrict φY).obj (GS.obj M))).val.obj U) :
      ((pbcRestrict b.hom).map (i.inv.app M)).val.app U x = x := by
    exact hiInv M U x
  have ha (x : (H.obj ((pbcRestrict q.hom).obj ((pbcRestrict φX).obj M))).val.obj U) :
      (H.map (a.hom.app M)).val.app U x = x := by
    change (a.hom.app M).val.app ((proEtaleBaseChange f).op.obj U) x = x
    simp only [a, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      restrictionComp_apply, restrictionComp_inv_apply]
  ext x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hl := (congrArg (fun y ↦
      (cd.hom.app ((pbcRestrict cS.hom).obj M)).val.app U
        (((pbcRestrict χ).map (cz.hom.app M)).val.app U y)) (hd x)).trans
    ((congrArg (fun y ↦ (cd.hom.app ((pbcRestrict cS.hom).obj M)).val.app U y)
      (hcz x)).trans (cdApp ((pbcRestrict cS.hom).obj M) U x))
  have hr := (congrArg (fun y ↦ (H.map (a.hom.app M)).val.app U
      ((cp.hom.app ((pbcRestrict φX).obj M)).val.app U y)) (hi x)).trans
    ((congrArg (fun y ↦ (H.map (a.hom.app M)).val.app U y)
      (cpApp ((pbcRestrict φX).obj M) U x)).trans (ha x))
  exact hl.trans hr.symm

end AlgebraicGeometry.Scheme
