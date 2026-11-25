/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenRestrictionNormalization
import WeilConjectures.AlgebraicGeometry.MayerVietorisRestrictionChainQuotientTransport

/-! # Complex localization of the open restriction square

Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: lem-pc-mayer-vietoris-image-restriction-localization).
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

/-- Complex localization of the open restriction square.
Source: Stacks Tags 08FE and 079V; the four-factor unit equation in
`schemeMVOpenRestriction_unit_normalization`.

Proof: apply that equation to the homotopy quotient of I. Transport the units
through mapHomotopyCategoryFactors and quotientCompQhIso to obtain the complex
localization maps. For the exact restrictions, mapDerivedCategoryFactorsh on
the quotient of I is the composite of mapDerivedCategoryFactors with those
same quotient comparisons. Substitute its defining factorization on both
sides. The homotopy open-restriction map is the quotient of the termwise
underived restriction isomorphism, with identity composition factors. By
naturality, the quotient factors next to each unit cancel. The remaining
three factors on either side give the forward unit square. Postcompose it with
G of the inverse exact-restriction factor on X and with the inverse derived
restriction comparison. Functoriality cancels the hom/inverse restriction factors,
and the comparison followed by its inverse is the identity. This gives the displayed
inverse-normalized identity, with its four-map composite named by
schemeMVRestrictionLocalizationChain. No open direct
image occurs in this square, and no K-injectivity of I or h_*I is required.
The formula remains valid for empty and full opens and identity morphisms.
(blueprint: lem-pc-mayer-vietoris-image-restriction-localization). -/
theorem schemeMV_image_restriction_localization
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (schemeMVRestrictionLocalizationChain X Y h W I) ≫
      (schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I) =
    (schemeMVDerivedRestriction Y W).map ((schemeMVDirectImageLocalization h).app I) := by
  let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
  let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
  let LY := schemeOpenRestriction Y W
  let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  have hn := schemeMVOpenRestriction_unit_normalization X Y h W K
  rw [schemeMV_restriction_chain_quotient_transport]
  rw [← hn]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  simp only [K, Iso.hom_inv_id_app_assoc]
  have ha := (schemeMVOpenRestrictionComparison h W).hom.naturality
    ((DerivedCategory.quotientCompQhIso _).hom.app I)
  dsimp only [Functor.comp_map] at ha
  rw [← reassoc_of% ha]
  simp only [Iso.hom_inv_id_app]
  simp [schemeMVDirectImageLocalization, Functor.map_comp, Category.assoc]


end AlgebraicGeometry
