/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain
import WeilConjectures.AlgebraicGeometry.MayerVietorisCompositionLeftNormalization
import WeilConjectures.AlgebraicGeometry.MayerVietorisCompositionRightNormalization

/-! # Complex localization of the open composition square

Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: lem-pc-mayer-vietoris-image-composition-localization).
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

/-- Core composition identity before combining the final derived map factors.
This is the unit-transport calculation from the open-composition normalization;
the final functorial reassociation is handled by the theorem below.

Proof: apply the open-composition unit normalization to the homotopy quotient of the
restricted complex, transport the units through the quotient comparison isomorphisms,
and expand the image component. Naturality and associativity identify the resulting
four-map composite with the explicit restriction-localization chain and the inverse
restriction comparison.
(source: Stacks Project, Tags 08FE and 0D5T)
(blueprint: lem-pc-mayer-vietoris-image-composition-localization-core) -/
theorem schemeMV_image_composition_localization_core
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)
    let R := schemeDerivedDirectImage W.ι
    (schemeMVDirectImageLocalization h).app (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I) ≫
      (schemeDerivedDirectImage h).map (schemeMVOpenImageLocalization X (h ⁻¹ᵁ W) I) ≫
      (schemeMVOpenComparison h W (DerivedCategory.Q.obj I)).hom =
    DerivedCategory.Q.map (schemeMVImageComponent h W I (F.obj I) (𝟙 _)) ≫
      schemeMVOpenImageLocalization Y W (F.obj I) ≫
      R.map (schemeMVRestrictionLocalizationChain X Y h W I) ≫
      R.map ((schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I)) := by
  have hleft := schemeMV_composition_left_normalization X Y h W I
  have hright := schemeMV_composition_right_normalization X Y h W I
  exact hleft.trans hright.symm

/-- Complex localization of the open composition square.
Source: Stacks Tags 0D5T and 08FE; the determining unit equations in
`schemeMVOpenComposition_unit_normalization`.

Proof: apply schemeMVOpenComposition_unit_normalization to the homotopy quotient
of the restricted complex J. Transport its units through mapHomotopyCategoryFactors
and quotientCompQhIso, whose components are identity quotient comparisons. Expand
schemeMVImageComponent degreewise: its sectionwise isomorphism is the open-composition
map followed by the open direct image of the inverse underived restriction isomorphism.
This follows from pushforwardCongr = eqToIso and the associator/whiskering formulas.
Naturality of the open direct-image localization unit moves that inverse restriction
isomorphism across the unit. Cancel it against the hom of the restriction isomorphism
on the right. Naturality of the derived composition comparison moves the inverse exact
restriction factor from QJ to derived restriction of QI on the left. Finally insert the
hom and inverse of the exact restriction factor on Y to recognize its open-image
localization map. The remaining four-map composite is
schemeMVRestrictionLocalizationChain. Postcompose both sides by the open derived
direct image of the inverse derived restriction comparison. Functoriality combines
the final two maps on the right; the definition of schemeMVOpenComparison identifies
the left side. This postcomposition uses no unit normalization property of that
restriction comparison, which is the separate restriction-localization obligation.
No K-injectivity is used here.
Empty and full opens and identity morphisms are included by the same unit equations.
(blueprint: lem-pc-mayer-vietoris-image-composition-localization). -/
theorem schemeMV_image_composition_localization
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)
    let R := schemeDerivedDirectImage W.ι
    (schemeMVDirectImageLocalization h).app (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I) ≫
      (schemeDerivedDirectImage h).map (schemeMVOpenImageLocalization X (h ⁻¹ᵁ W) I) ≫
      (schemeMVOpenComparison h W (DerivedCategory.Q.obj I)).hom =
    DerivedCategory.Q.map (schemeMVImageComponent h W I (F.obj I) (𝟙 _)) ≫
      schemeMVOpenImageLocalization Y W (F.obj I) ≫
      R.map (schemeMVRestrictionLocalizationChain X Y h W I ≫
        (schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I)) := by
  have hc := schemeMV_image_composition_localization_core X Y h W I
  dsimp only at hc ⊢
  simpa only [Functor.map_comp, Category.assoc] using hc

end AlgebraicGeometry
