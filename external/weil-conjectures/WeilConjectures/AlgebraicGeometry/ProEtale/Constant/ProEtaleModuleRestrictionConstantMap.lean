/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement

/-!
# Constant-scalar encoding and maps of constant rings

For a ring map `g : B →+* B'`, restricting scalars along the induced map of constant ring
sheaves and then encoding by constant scalars agrees with encoding first and then restricting
the scalars of the fixed coefficient ring along `g`. Both are the identity on sections.

## References

* Stacks Project, Tags 093I and 03CY
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {B B' : Type u} [CommRing B] [CommRing B'] (g : B →+* B')

/-- The map of constant ring sheaves induced by `g` sends the constant section of `b` to the
constant section of `g b`. -/
theorem adicConstantMap_scalarUnit (W : X.ProEtᵒᵖ) (b : ULift.{u + 1} B) :
    (adicConstantMap X g).hom.app W ((proEtaleModuleScalarUnit X B).app W b) =
      (proEtaleModuleScalarUnit X B').app W (ULift.up (g b.down)) := by
  let q : CommRingCat.of (ULift.{u + 1} B) ⟶ CommRingCat.of (ULift.{u + 1} B') :=
    CommRingCat.ofHom (RingHom.ulift g)
  exact (congrArg (fun f ↦ f.app W b)
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map q))).symm

/-- The sectionwise identity from restriction along the constant map, followed by
constant-scalar encoding, to the encoding followed by restriction along `g`. -/
def proEtaleModuleRestrictionConstantMapHom
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (adicConstantRing X B'))) :
    (proEtaleModuleRestriction X B).obj ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (adicConstantMap X g))).obj M) ⟶
      (sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} g))).obj
          ((proEtaleModuleRestriction X B').obj M) where
  hom.app U := ModuleCat.ofHom
    (X := ((proEtaleModuleRestriction X B).obj ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (adicConstantMap X g))).obj
            M)).obj.obj U)
    (Y := ((sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} g))).obj
          ((proEtaleModuleRestriction X B').obj M)).obj.obj U)
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ congrArg (fun s ↦ s • (show M.val.obj U from x))
        (adicConstantMap_scalarUnit X g U c) }
  hom.naturality _ _ _ := rfl

/-- The inverse of `proEtaleModuleRestrictionConstantMapHom`, again the identity on
sections. -/
def proEtaleModuleRestrictionConstantMapInv
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (adicConstantRing X B'))) :
    (sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} g))).obj
          ((proEtaleModuleRestriction X B').obj M) ⟶
      (proEtaleModuleRestriction X B).obj ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (adicConstantMap X g))).obj M) where
  hom.app U := ModuleCat.ofHom
    (Y := ((proEtaleModuleRestriction X B).obj ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (adicConstantMap X g))).obj
            M)).obj.obj U)
    (X := ((sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} g))).obj
          ((proEtaleModuleRestriction X B').obj M)).obj.obj U)
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ congrArg (fun s ↦ s • (show M.val.obj U from x))
        (adicConstantMap_scalarUnit X g U c).symm }
  hom.naturality _ _ _ := rfl

/-- The constant-scalar encoding intertwines restriction along a map of constant ring
sheaves with restriction of the fixed coefficient ring. Both composites are the identity on
sections. -/
def proEtaleModuleRestrictionConstantMapIso :
    SheafOfModules.restrictScalars.{u + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (adicConstantMap X g)) ⋙
      proEtaleModuleRestriction X B ≅
    proEtaleModuleRestriction X B' ⋙ sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} g)) :=
  NatIso.ofComponents (fun M ↦
    { hom := proEtaleModuleRestrictionConstantMapHom X g M
      inv := proEtaleModuleRestrictionConstantMapInv X g M
      hom_inv_id := rfl
      inv_hom_id := rfl })
    (fun _ ↦ by ext; rfl)

end AlgebraicGeometry.Scheme
