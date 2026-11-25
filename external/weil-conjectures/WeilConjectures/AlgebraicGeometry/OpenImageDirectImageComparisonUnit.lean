/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
import all WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenComparisonUnit
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare

/-! # The ordinary open-image comparison and its unit

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-open-image-direct-image-comparison-unit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry

/-- The ordinary open-image comparison, assembled from the fixed restriction
and direct-image composition identifications.
Source: Stacks Project, Tag 08FE.
(blueprint: lem-pc-open-image-direct-image-comparison-unit). -/
@[irreducible]
def schemeOpenImageDirectImageComparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    (U : Y.Opens) :
    schemeOpenModuleImage X (h ⁻¹ᵁ U) ⋙
        RingedSpace.moduleDirectImage h.toLRSHom.toShHom ≅
      RingedSpace.moduleDirectImage h.toLRSHom.toShHom ⋙ schemeOpenModuleImage Y U :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (schemeOpenRestriction X (h ⁻¹ᵁ U))
      (schemeMVUnderivedOpenComposition h U) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (schemeMVUnderivedOpenRestriction h U).symm
      (Scheme.Modules.pushforward U.ι) ≪≫
    Functor.associator _ _ _

attribute [local irreducible] schemeMVUnderivedOpenComposition
  schemeMVUnderivedOpenRestriction schemeOpenModuleAdjunction RingedSpace.moduleDirectImage

private theorem unit_of_homotopy_counit
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    [Preadditive C] [Preadditive D] [Preadditive A] [Preadditive B]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject A] [HasZeroObject B]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B]
    {LX : C ⥤ A} {RX : A ⥤ C} {LY : D ⥤ B} {RY : B ⥤ D}
    (aX : LX ⊣ RX) (aY : LY ⊣ RY) (F : C ⥤ D) (G : A ⥤ B)
    [LX.Additive] [RX.Additive] [LY.Additive] [RY.Additive]
    [F.Additive] [G.Additive]
    (α : F ⋙ LY ≅ LX ⋙ G) (β : RX ⋙ F ≅ G ⋙ RY)
    (M : C)
    (hcAll : ∀ K : HomotopyCategory A (.up ℤ),
      (LY.mapHomotopyCategory (.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso β (.up ℤ) ≪≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app K) ≫
          (aY.mapHomotopyCategory (.up ℤ)).counit.app
            ((G.mapHomotopyCategory (.up ℤ)).obj K) =
        (Functor.mapHomotopyCategoryCompIso α (.up ℤ) ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (LX ⋙ G)) (.up ℤ)).symm).hom.app
            ((RX.mapHomotopyCategory (.up ℤ)).obj K) ≫
          (G.mapHomotopyCategory (.up ℤ)).map
            ((aX.mapHomotopyCategory (.up ℤ)).counit.app K)) :
    F.map (aX.unit.app M) ≫ β.hom.app (LX.obj M) ≫ RY.map (α.inv.app M) =
      aY.unit.app (F.obj M) := by
  let αH := Functor.mapHomotopyCategoryCompIso α (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (LX ⋙ G)) (.up ℤ)).symm
  let βH := Functor.mapHomotopyCategoryCompIso β (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm
  generalize hI : (HomologicalComplex.single
    C (.up ℤ) (0 : ℤ)).obj M = I
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  have hc := hcAll
    ((LX.mapHomotopyCategory (.up ℤ)).obj K)
  have hu := unit_of_counit
    (aX.mapHomotopyCategory (.up ℤ))
    (aY.mapHomotopyCategory (.up ℤ))
    (F.mapHomotopyCategory (.up ℤ)) (G.mapHomotopyCategory (.up ℤ))
    αH βH K hc
  let Q := HomotopyCategory.quotient
    D (.up ℤ)
  have hx : (aX.mapHomotopyCategory (.up ℤ)).unit.app K =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((aX.mapHomologicalComplex (.up ℤ)).unit.app I) :=
    Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
      aX I
  have hy : (aY.mapHomotopyCategory (.up ℤ)).unit.app
      ((F.mapHomotopyCategory (.up ℤ)).obj K) = Q.map
        ((aY.mapHomologicalComplex (.up ℤ)).unit.app
          ((F.mapHomologicalComplex (.up ℤ)).obj I)) :=
    Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
      aY ((F.mapHomologicalComplex (.up ℤ)).obj I)
  rw [hx, hy] at hu
  have hβ : βH.hom.app
      ((LX.mapHomotopyCategory (.up ℤ)).obj K) =
      Q.map ((β.hom.mapHomologicalComplex
        (.up ℤ)).app ((LX.mapHomologicalComplex (.up ℤ)).obj I)) := by
    dsimp only [βH, Iso.trans_hom, NatTrans.comp_app,
      Iso.symm_hom]
    change Q.map _ ≫ Q.map (𝟙 _) = _
    exact (congrArg (fun k ↦ Q.map _ ≫ k) (Q.map_id _)).trans (Category.comp_id _)
  let Q' := HomotopyCategory.quotient
    B (.up ℤ)
  have hα : αH.inv.app K =
      Q'.map ((α.inv.mapHomologicalComplex
          (.up ℤ)).app I) := by
    dsimp only [αH, Iso.trans_inv, NatTrans.comp_app,
      Iso.symm_inv]
    change Q'.map (𝟙 _) ≫ Q'.map _ = _
    exact (congrArg (fun k ↦ k ≫ Q'.map _) (Q'.map_id _)).trans (Category.id_comp _)
  erw [hβ, hα] at hu
  simp only [Functor.mapHomotopyCategory_map] at hu
  let p := (F.mapHomologicalComplex (.up ℤ)).map
      ((aX.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
    ((β.hom.mapHomologicalComplex (.up ℤ)).app
      ((LX.mapHomologicalComplex (.up ℤ)).obj I)) ≫
    (RY.mapHomologicalComplex (.up ℤ)).map
      ((α.inv.mapHomologicalComplex (.up ℤ)).app I)
  let q := (aY.mapHomologicalComplex (.up ℤ)).unit.app
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  have hu' : Q.map p = Q.map q := by
    dsimp only [p]
    rw [Q.map_comp, Q.map_comp]
    exact hu
  subst I
  let H := HomotopyCategory.homotopyOfEq p q hu'
  have he := H.comm (0 : ℤ)
  simp only [dNext, prevD, AddMonoidHom.mk'_apply, Functor.id_obj,
    Functor.mapHomologicalComplex_obj_d, HomologicalComplex.single_obj_d,
    Functor.map_zero, zero_comp, comp_zero, zero_add, add_zero] at he
  change F.map (aX.unit.app M) ≫ β.hom.app (LX.obj M) ≫
    RY.map (α.inv.app M) = aY.unit.app (F.obj M) at he
  exact he

/-- The ordinary comparison carries the inverse-image-open unit to the open unit.
Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: lem-pc-open-image-direct-image-comparison-unit).
Proof: The existing underived open counit square is stated on homotopy
categories. The generic unit_of_counit calculation applies the open adjunction
Hom equivalences, counit naturality, and the two triangle identities to give
its unit square there. Represent M by a complex concentrated in degree zero.
The quotient formulas for mapped units and comparison isomorphisms express
this square as equality of the images of two actual chain maps. Take a
homotopy witnessing that equality. Both complexes have zero differentials,
so its degree-zero equation is equality of the ordinary module maps. Finally
expand only the five formal associator and whiskering factors constructing
the comparison; their identity components cancel. This argument includes
empty and full opens, identity h, and zero M without extra assumptions. -/
theorem schemeOpenImageDirectImageComparison_unit
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U : Y.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map
        ((schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)).unit.app M) ≫
        (schemeOpenImageDirectImageComparison h U).hom.app M =
      (schemeOpenModuleAdjunction Y U).unit.app
        ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).obj M) := by
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ U)
  let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom
  let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
  let G := RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom
  let RY := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let LY := schemeOpenRestriction Y U
  let aX : LX ⊣ RX := by
    with_unfolding_all exact schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)
  let aY : LY ⊣ RY := by
    with_unfolding_all exact schemeOpenModuleAdjunction Y U
  have hu := unit_of_homotopy_counit aX aY F G
    (schemeMVUnderivedOpenRestriction h U) (schemeMVUnderivedOpenComposition h U) M
    (fun K ↦ schemeMVUnderivedOpenCounit_square X Y h U K)
  with_unfolding_all
    change F.map (aX.unit.app M) ≫
      ((((𝟙 _ ≫ (schemeMVUnderivedOpenComposition h U).hom.app (LX.obj M)) ≫ 𝟙 _) ≫
        RY.map ((schemeMVUnderivedOpenRestriction h U).inv.app M)) ≫ 𝟙 _) =
      aY.unit.app (F.obj M)
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hu

end AlgebraicGeometry
