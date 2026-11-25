/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCompositionCounit

/-! # Compatibility of the canonical single-open direct-image comparison

Source: Stacks Project, Tags 08FE, 0D5T and 08BV.
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

private theorem counit_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {LX : C ⥤ C'} {RX : C' ⥤ C} {LY : D ⥤ D'} {RY : D' ⥤ D}
    (a : LX ⊣ RX) (b : LY ⊣ RY) (F : C ⥤ D) (G : C' ⥤ D')
    (α : F ⋙ LY ≅ LX ⋙ G) (β : RX ⋙ F ≅ G ⋙ RY)
    {A B : C'} (e : A ≅ B)
    (hA : LY.map (β.hom.app A) ≫ b.counit.app (G.obj A) =
      α.hom.app (RX.obj A) ≫ G.map (a.counit.app A)) :
    LY.map (β.hom.app B) ≫ b.counit.app (G.obj B) =
      α.hom.app (RX.obj B) ≫ G.map (a.counit.app B) := by
  let m : (RX ⋙ F) ⋙ LY ⟶ G :=
    Functor.whiskerRight β.hom LY ≫ (Functor.associator G RY LY).hom ≫
      Functor.whiskerLeft G b.counit ≫ G.rightUnitor.hom
  let n : (RX ⋙ F) ⋙ LY ⟶ G :=
    (Functor.associator RX F LY).hom ≫ Functor.whiskerLeft RX α.hom ≫
      (Functor.associator RX LX G).inv ≫ Functor.whiskerRight a.counit G ≫
      G.leftUnitor.hom
  have hi : m.app A = n.app A := by simpa [m, n] using hA
  have he : m.app B = n.app B := by
    apply (cancel_epi (((RX ⋙ F) ⋙ LY).map e.hom)).mp
    rw [m.naturality, n.naturality, hi]
  simpa [m, n] using he

private theorem unit_of_counit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {LX : C ⥤ C'} {RX : C' ⥤ C} {LY : D ⥤ D'} {RY : D' ⥤ D}
    (a : LX ⊣ RX) (b : LY ⊣ RY) (F : C ⥤ D) (G : C' ⥤ D')
    (α : F ⋙ LY ≅ LX ⋙ G) (β : RX ⋙ F ≅ G ⋙ RY) (E : C)
    (hc : LY.map (β.hom.app (LX.obj E)) ≫ b.counit.app (G.obj (LX.obj E)) =
      α.hom.app (RX.obj (LX.obj E)) ≫ G.map (a.counit.app (LX.obj E))) :
    F.map (a.unit.app E) ≫ β.hom.app (LX.obj E) ≫ RY.map (α.inv.app E) =
      b.unit.app (F.obj E) := by
  apply (b.homEquiv _ _).symm.injective
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [b.homEquiv_symm_unit]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [b.counit.naturality (α.inv.app E)]
  simp only [Functor.id_map, Functor.comp_obj]
  rw [← Category.assoc (LY.map (β.hom.app (LX.obj E)))
    (b.counit.app (G.obj (LX.obj E))) (α.inv.app E), hc]
  simp only [Category.assoc]
  have hn := α.hom.naturality (a.unit.app E)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← Category.assoc, hn, Category.assoc]
  rw [← G.map_comp_assoc, a.left_triangle_components, G.map_id, Category.id_comp]
  exact α.hom_inv_id_app E

private theorem comparison_hom
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (U : Y.Opens)
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ U).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ U) ⋙ schemeDerivedDirectImage U.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ U).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ U) U.ι)
    (E : schemeDerivedCategory X) :
    (schemeMVOpenComparison h U E).hom =
      β.hom.app ((schemeMVDerivedRestriction X (h ⁻¹ᵁ U)).obj E) ≫
        (schemeDerivedDirectImage U.ι).map ((schemeMVOpenRestrictionComparison h U).inv.app E) := by
  unfold schemeMVOpenComparison
  rw [← hβ]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom]

private theorem composition_counit
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (U : Y.Opens)
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ U).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ U) ⋙ schemeDerivedDirectImage U.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ U).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ U) U.ι)
    (A : schemeDerivedCategory (h ⁻¹ᵁ U).toScheme) :
    (schemeMVDerivedRestriction Y U).map
        (β.hom.app A) ≫
        (schemeMVAdjunction Y U).counit.app ((schemeDerivedDirectImage (h ∣_ U)).obj A) =
      (schemeMVOpenRestrictionComparison h U).hom.app
          ((schemeDerivedDirectImage (h ⁻¹ᵁ U).ι).obj A) ≫
        (schemeDerivedDirectImage (h ∣_ U)).map
          ((schemeMVAdjunction X (h ⁻¹ᵁ U)).counit.app A) := by
  let RX := schemeDerivedDirectImage (h ⁻¹ᵁ U).ι
  let F := schemeDerivedDirectImage h
  let G := schemeDerivedDirectImage (h ∣_ U)
  let LY := schemeMVDerivedRestriction Y U
  let RY := schemeDerivedDirectImage U.ι
  let LX := schemeMVDerivedRestriction X (h ⁻¹ᵁ U)
  let a : LX ⊣ RX := schemeMVAdjunction X (h ⁻¹ᵁ U)
  let b : LY ⊣ RY := schemeMVAdjunction Y U
  let α : F ⋙ LY ≅ LX ⋙ G := schemeMVOpenRestrictionComparison h U
  let I := schemeMVResolution (h ⁻¹ᵁ U).toScheme A
  change LY.map (β.hom.app A) ≫ b.counit.app (G.obj A) =
    α.hom.app (RX.obj A) ≫ G.map (a.counit.app A)
  have hi : LY.map (β.hom.app (DerivedCategory.Q.obj I)) ≫
      b.counit.app (G.obj (DerivedCategory.Q.obj I)) =
    α.hom.app (RX.obj (DerivedCategory.Q.obj I)) ≫
      G.map (a.counit.app (DerivedCategory.Q.obj I)) := by
    exact schemeMVOpenComposition_counit_Q X Y h U β hβ I
  exact counit_transport a b F G α β (schemeMVResolutionIso (h ⁻¹ᵁ U).toScheme A) hi

private theorem unit_with_composition
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (U : Y.Opens)
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ U).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ U) ⋙ schemeDerivedDirectImage U.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ U).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ U) U.ι)
    (E : schemeDerivedCategory X) :
    (schemeDerivedDirectImage h).map ((schemeMVAdjunction X (h ⁻¹ᵁ U)).unit.app E) ≫
        (schemeMVOpenComparison h U E).hom =
      (schemeMVAdjunction Y U).unit.app ((schemeDerivedDirectImage h).obj E) := by
  let RX := schemeDerivedDirectImage (h ⁻¹ᵁ U).ι
  let F := schemeDerivedDirectImage h
  let G := schemeDerivedDirectImage (h ∣_ U)
  let LY := schemeMVDerivedRestriction Y U
  let RY := schemeDerivedDirectImage U.ι
  let LX := schemeMVDerivedRestriction X (h ⁻¹ᵁ U)
  let a : LX ⊣ RX := schemeMVAdjunction X (h ⁻¹ᵁ U)
  let b : LY ⊣ RY := schemeMVAdjunction Y U
  let α : F ⋙ LY ≅ LX ⋙ G := schemeMVOpenRestrictionComparison h U
  rw [comparison_hom X Y h U β hβ E]
  have hc : LY.map (β.hom.app (LX.obj E)) ≫ b.counit.app (G.obj (LX.obj E)) =
      α.hom.app (RX.obj (LX.obj E)) ≫ G.map (a.counit.app (LX.obj E)) := by
    exact composition_counit X Y h U β hβ (LX.obj E)
  have ht := unit_of_counit a b F G α β E hc
  exact ht

/-- Direct image and the canonical open comparison carry a single restriction unit
on X to the corresponding restriction unit on Y. No cover or triangle is involved.
Source: Stacks Project, Tag 08FE, proof on K-injective representatives; Tag 0D5T,
canonical composition of derived direct images; Tag 08BV, first proof paragraph.

Proof: First apply schemeMVOpenComposition_counit_Q on a K-injective representative
of an object A on the inverse-image open. The two counit composites are natural
transformations, so their equality transports along schemeMVResolutionIso to every A.
Transpose the desired unit equation under the Y-open adjunction Hom equivalence.
Expand the comparison into its composition factor and the inverse open-restriction
factor. Counit naturality moves the latter past the Y counit; apply the extended
counit computation at A = LX(E). Naturality of the restriction comparison for the
X-open unit reduces the remaining middle factor to the X-adjunction left triangle
identity. The restriction comparison and its inverse cancel. Injectivity of the
Hom equivalence proves the original equation. This applies to empty and full opens
and requires no cover. The only postponed part is the separately stated normalized
counit computation, which does not contain the unit equation being proved here.
(blueprint: lem-pc-derived-mayer-vietoris-open-comparison-unit). -/
theorem schemeMVOpenComparison_unit
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (U : Y.Opens) (E : schemeDerivedCategory X) :
    (schemeDerivedDirectImage h).map ((schemeMVAdjunction X (h ⁻¹ᵁ U)).unit.app E) ≫
        (schemeMVOpenComparison h U E).hom =
      (schemeMVAdjunction Y U).unit.app ((schemeDerivedDirectImage h).obj E) := by
  exact unit_with_composition X Y h U
    ((schemeMVDirectImageComposition (h ⁻¹ᵁ U).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ U) U.ι) rfl E

end AlgebraicGeometry
