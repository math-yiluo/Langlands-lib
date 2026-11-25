/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData

/-! # The explicit restriction-localization chain

Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: def-pc-mayer-vietoris-restriction-localization-chain).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

/-- The restriction/localization chain from restricted h_*I to R(h|W)_* of
restricted QI. Source: Stacks Tags 08FE and 079V.

Construction: use the exact Y-restriction factor, then the localized underived
restriction/direct-image comparison, then the direct-image unit on the restricted
complex, then the derived restricted direct image of the inverse X-restriction factor.
All four maps are the existing explicit constructions; no existence witness is chosen.
Irreducibility keeps their construction out of downstream categorical conversions;
its unit compatibility is stated in MayerVietorisImageRestrictionLocalization.
(blueprint: def-pc-mayer-vietoris-restriction-localization-chain). -/
@[irreducible]
def schemeMVRestrictionLocalizationChain
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (schemeMVDerivedRestriction Y W).obj
        (DerivedCategory.Q.obj
          (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
            (.up ℤ)).obj I)) ⟶
      (schemeDerivedDirectImage (h ∣_ W)).obj
        ((schemeMVDerivedRestriction X (h ⁻¹ᵁ W)).obj (DerivedCategory.Q.obj I)) :=
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
  let LY := schemeOpenRestriction Y W
  let J := (LX.mapHomologicalComplex (.up ℤ)).obj I
  let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
    (.up ℤ)
  (LY.mapDerivedCategoryFactors.hom.app (F.obj I) ≫
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (schemeMVUnderivedOpenRestriction h W).hom
        (.up ℤ)).app I) ≫
    (schemeMVDirectImageLocalization (h ∣_ W)).app J) ≫
    (schemeDerivedDirectImage (h ∣_ W)).map (LX.mapDerivedCategoryFactors.inv.app I)

end AlgebraicGeometry
