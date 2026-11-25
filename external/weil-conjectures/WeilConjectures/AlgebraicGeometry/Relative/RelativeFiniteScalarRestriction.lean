/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteCoefficientTransport
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement

/-! # Ordinary scalar restriction and the constructed coefficient transport

## References

* Stacks Project, Modules on Sites, Tags 03CY and 03D8
* Sites, Tag 03A0
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem coefficientNaturality {X Y : Scheme.{u}} (g : Y ⟶ X)
    {B R : Type (u + 1)} [CommRing B] [CommRing R] (f : B →+* R) :
    (constantSheaf (proEtaleModelTopology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom f) ≫ (relativeFiniteModelCoefficient g R).hom =
      (relativeFiniteModelCoefficient g B).hom ≫
        ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
          CommRingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).map
            ((adicTowerInverseImage g).map
              ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
                (CommRingCat.ofHom f))) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
    infer_instance
  have (A : CommRingCat.{u + 1}) : IsIso ((proEtaleConstantComparison g).app A) :=
    relativeFiniteConstantInverseImage_isIso g A
  have : IsIso (proEtaleConstantComparison g) := NatIso.isIso_of_isIso_app _
  let c := asIso (proEtaleConstantComparison g)
  let β := (e.constantSheafSheafCongrIso (ProEt.topology Y)
      (proEtaleModelTopology Y) CommRingCat.{u + 1} terminalIsTerminal).symm ≪≫
    Functor.isoWhiskerRight c.symm
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
        CommRingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y))
  simpa only [β, relativeFiniteModelCoefficient, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    c, asIso_inv, NatIso.isIso_inv_app, Functor.mapIso_hom, Iso.app_inv,
    Functor.comp_map, e, proEtaleConstantComparison] using β.hom.naturality (CommRingCat.ofHom f)

/-- Ordinary restriction of scalars commutes with the constructed small-site
transport. This comparison involves no derived functor or local model predicate. -/
theorem relativeFiniteScalarRestriction {X Y : Scheme.{u}} (g : Y ⟶ X)
    {B R : Type (u + 1)} [CommRing B] [CommRing R] (f : B →+* R) :
    Nonempty ((pbcRestrict ((adicTowerInverseImage g).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom f))) ⋙ relativeFiniteModelModules g B) ≅
      (relativeFiniteModelModules g R ⋙ CategoryTheory.ConstantCompletion.res
        ((constantSheaf (proEtaleModelTopology Y) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom f)))) := by
  let φ := (adicTowerInverseImage g).map
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom f))
  let ψ := (constantSheaf (proEtaleModelTopology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom f)
  let down := (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt)
  let E₁ := pbcRestrict φ ⋙ relativeFiniteModelModules g B
  let E₂ := relativeFiniteModelModules g R ⋙ CategoryTheory.ConstantCompletion.res ψ
  let RB := SheafOfModules.constantCoefficientRing (proEtaleModelTopology Y) B
  refine ⟨NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget RB).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)) ?_⟩
  · refine (show ((E₁.obj M).val.obj U : Type (u + 1)) ≃ₗ[RB.obj.obj U]
        (E₂.obj M).val.obj U from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    have hb := congrArg (fun a ↦ (a.hom.app U).hom b) (coefficientNaturality g f)
    change (φ.hom.app (down.op.obj U)).hom
        (((relativeFiniteModelCoefficient g B).hom.hom.app U).hom b) •
          (show M.val.obj (down.op.obj U) from m) =
      ((relativeFiniteModelCoefficient g R).hom.hom.app U).hom ((ψ.hom.app U).hom b) •
          (show M.val.obj (down.op.obj U) from m)
    exact congrArg (fun r ↦ r • (show M.val.obj (down.op.obj U) from m)) hb.symm
  · intro U V a
    ext x
    rfl
  · intro M N a
    ext U x
    rfl

end AlgebraicGeometry.Scheme
