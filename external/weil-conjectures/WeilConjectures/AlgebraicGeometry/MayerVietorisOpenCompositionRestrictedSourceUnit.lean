/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.MayerVietorisOpenCompositionComplexLocalization

/-! # Open composition units on a restricted source complex

Source: Stacks Project, Tags 08FE and 0D5T.
(blueprint: lem-pc-mayer-vietoris-open-composition-restricted-source-unit).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian
/-- The open-composition unit equation with its source in the open-image complex notation.
Source: Stacks Project, Tags 08FE, 0D5T and 079V.

Proof: put J equal to the termwise restriction of I. The open-image complex is
restriction followed by open pushforward in each degree. It is definitionally equal
to termwise open pushforward of J: both objects and differentials are obtained by
applying the same composite functor, and Scheme.Modules.pushforward is the ringed-space
module direct image of the scheme morphism. Apply
schemeMVOpenComposition_complex_localization to beta, its canonicality equation and J.
All three maps on each side are exactly the maps in that theorem.
No inverse exact restriction factor or derived restriction comparison enters this
argument. Empty opens, full opens, identity morphisms and arbitrary complexes satisfy
the same termwise identities; no injectivity or cover hypothesis is needed.
(blueprint: lem-pc-mayer-vietoris-open-composition-restricted-source-unit). -/
theorem schemeMVOpenComposition_restricted_source_unit
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ W).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ W) ⋙ schemeDerivedDirectImage W.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ W).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h W).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ W) W.ι)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let J := ((schemeOpenRestriction X (h ⁻¹ᵁ W)).mapHomologicalComplex (.up ℤ)).obj I
    let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
    let RY := RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom
    let b₀ := (Functor.mapHomologicalComplexCompIso
        (schemeMVUnderivedOpenComposition h W) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app J
    (schemeMVDirectImageLocalization h).app (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I) ≫
      (schemeDerivedDirectImage h).map
        ((schemeMVDirectImageLocalization (h ⁻¹ᵁ W).ι).app J) ≫
      β.hom.app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map b₀ ≫
      (schemeMVDirectImageLocalization W.ι).app
        ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage W.ι).map
        ((schemeMVDirectImageLocalization (h ∣_ W)).app J) := by
  exact schemeMVOpenComposition_complex_localization X Y h W β hβ
    (((schemeOpenRestriction X (h ⁻¹ᵁ W)).mapHomologicalComplex (.up ℤ)).obj I)

end AlgebraicGeometry
