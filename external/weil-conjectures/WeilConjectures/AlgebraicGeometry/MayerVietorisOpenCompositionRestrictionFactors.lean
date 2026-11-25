/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData

/-! # Restriction factors across open composition

Source: Stacks Project, Tags 08FE and 0D5T.
(blueprint: lem-pc-mayer-vietoris-open-composition-restriction-factors).
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

-- Keep the comparison and exact-derived constructions folded during specialization.
private lemma restriction_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : B ⥤ D) (j : A ⥤ B) (G : A ⥤ C) (k : C ⥤ D)
    (r : B ⥤ A) (s : D ⥤ C) (β : j ⋙ F ≅ G ⋙ k)
    (γ : F ⋙ s ≅ r ⋙ G) {P : A} {Q R : B}
    (u : R ⟶ j.obj P) (f : P ⟶ r.obj Q) :
    F.map (u ≫ j.map f) ≫ (β.app (r.obj Q) ≪≫ k.mapIso (γ.symm.app Q)).hom =
      F.map u ≫ β.hom.app P ≫ k.map (G.map f ≫ γ.inv.app Q) := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom]
  have hn := β.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [F.map_comp, Category.assoc, ← Category.assoc (F.map (j.map f)), hn]
  simp only [Category.assoc, Functor.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality moves the exact source-restriction factor through open composition.
Source: Stacks Project, Tags 08FE, 0D5T and 079V.

Proof: let f be the inverse exact restriction factor from QJ to restriction of QI.
The definition of schemeMVOpenImageLocalization is the open-localization unit followed
by the open derived direct image of f. The definition of schemeMVOpenComparison is the
component of beta at restriction of QI followed by the target-open derived direct image
of the inverse restriction comparison. Expand these two definitions and apply the
functorial composition equation for the derived direct image of h. Naturality of
beta.hom along f identifies Rh(Rj_X(f)) followed by the beta component at restriction
of QI with the beta component at QJ followed by Rj_Y(R(h|W)(f)). Associate the
composites and combine the two final maps using functoriality of Rj_Y. This gives the
stated equality without using the h-localization unit or the complex-composition map.
Only naturality and functoriality are used, so arbitrary complexes, empty and full
opens and identity morphisms are included; there is no injectivity or cover hypothesis.
(blueprint: lem-pc-mayer-vietoris-open-composition-restriction-factors). -/
theorem schemeMVOpenComposition_restriction_factors
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
    let J := (LX.mapHomologicalComplex (.up ℤ)).obj I
    let β := (schemeMVDirectImageComposition (h ⁻¹ᵁ W).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h W).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ W) W.ι
    (schemeDerivedDirectImage h).map (schemeMVOpenImageLocalization X (h ⁻¹ᵁ W) I) ≫
      (schemeMVOpenComparison h W (DerivedCategory.Q.obj I)).hom =
    (schemeDerivedDirectImage h).map ((schemeMVDirectImageLocalization (h ⁻¹ᵁ W).ι).app J) ≫
      β.hom.app (DerivedCategory.Q.obj J) ≫
      (schemeDerivedDirectImage W.ι).map
        ((schemeDerivedDirectImage (h ∣_ W)).map (LX.mapDerivedCategoryFactors.inv.app I) ≫
          (schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I)) := by
  intro LX J β
  exact restriction_factors (schemeDerivedDirectImage h)
    (schemeDerivedDirectImage (h ⁻¹ᵁ W).ι) (schemeDerivedDirectImage (h ∣_ W))
    (schemeDerivedDirectImage W.ι) (schemeMVDerivedRestriction X (h ⁻¹ᵁ W))
    (schemeMVDerivedRestriction Y W) β (schemeMVOpenRestrictionComparison h W)
    (P := DerivedCategory.Q.obj J) (Q := DerivedCategory.Q.obj I)
    (R := DerivedCategory.Q.obj (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I))
    ((schemeMVDirectImageLocalization (h ⁻¹ᵁ W).ι).app J)
    (LX.mapDerivedCategoryFactors.inv.app I)

end AlgebraicGeometry
