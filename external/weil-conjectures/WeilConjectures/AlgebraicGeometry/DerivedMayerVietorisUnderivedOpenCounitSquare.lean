/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
import WeilConjectures.AlgebraicGeometry.OrdinaryOpenCounitSquare

/-! # The underived open counit square

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-mayer-vietoris-underived-open-counit-square).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry


section

universe v

variable {A B C D : Type u} [Category.{v} A] [Category.{v} B]
  [Category.{v} C] [Category.{v} D]
  [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
  {LX : A ⥤ B} {RX : B ⥤ A} {LY : C ⥤ D} {RY : D ⥤ C}
  {F : A ⥤ C} {G : B ⥤ D}
  [LX.Additive] [RX.Additive] [LY.Additive] [RY.Additive]
  [F.Additive] [G.Additive]
  [(HomotopyCategory.quotient A (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences A (.up ℤ))]
  [(HomotopyCategory.quotient B (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences B (.up ℤ))]
  [(HomotopyCategory.quotient C (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences C (.up ℤ))]
  [(HomotopyCategory.quotient D (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences D (.up ℤ))]
private theorem lift_open_counit_square (aX : LX ⊣ RX) (aY : LY ⊣ RY)
    (α : F ⋙ LY ≅ LX ⋙ G) (β : RX ⋙ F ≅ G ⋙ RY)
    (h : ∀ M, LY.map (β.hom.app M) ≫ aY.counit.app (G.obj M) =
      α.hom.app (RX.obj M) ≫ G.map (aX.counit.app M))
    (K : HomotopyCategory B (.up ℤ)) :
    (LY.mapHomotopyCategory (.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso β (.up ℤ) ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app K) ≫
        (aY.mapHomotopyCategory (.up ℤ)).counit.app
          ((G.mapHomotopyCategory (.up ℤ)).obj K) =
      (Functor.mapHomotopyCategoryCompIso α (.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (LX ⋙ G)) (.up ℤ)).symm).hom.app
          ((RX.mapHomotopyCategory (.up ℤ)).obj K) ≫
        (G.mapHomotopyCategory (.up ℤ)).map
          ((aX.mapHomotopyCategory (.up ℤ)).counit.app K) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hY := Adjunction.mapHomotopyCategory_counit_app_quotient (.up ℤ) aY
    ((G.mapHomologicalComplex (.up ℤ)).obj M)
  erw [hY, Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _ =
    (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, Iso.refl_inv, NatTrans.id_app]
  change LY.map (β.hom.app (M.X n) ≫ 𝟙 _) ≫
      aY.counit.app (G.obj (M.X n)) =
    (α.hom.app (RX.obj (M.X n)) ≫ 𝟙 _) ≫ G.map (aX.counit.app (M.X n))
  rw [Category.comp_id, Category.comp_id]
  exact h (M.X n)

end

set_option linter.unusedVariables false in
/-- The sectionwise comparison square respects the two underived open counits,
after passage to the homotopy category.
Source: Stacks Tags 08FE and 08BV.
Proof: on an open W of U, both composites are the restriction identification of
sections of I over g inverse image W. Use restrictAdjunction_counit_app_app for
the two counits and the sectionwise formulas for pushforwardComp and
pushforwardCongr. Transport along overFunctorEquiv, which is the identification
used to define schemeOpenModuleAdjunction and schemeMVUnderivedOpenRestriction.
The equalities are natural in I and commute with its differentials. Apply the
termwise functors, then the homotopy quotient; the quotient counit formula
mapHomotopyCategory_counit_app_quotient identifies their counits. Every homotopy
object is a quotient of a complex, so this gives the displayed equation for all K.
For the empty open this is the unique map between zero objects; for the full open
it is the same sectionwise identity. No derived comparison occurs here.
(blueprint: lem-pc-mayer-vietoris-underived-open-counit-square). -/
theorem schemeMVUnderivedOpenCounit_square
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U : Y.Opens)
    (K : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom
    let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
    let G := RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom
    let LX := schemeOpenRestriction X (h ⁻¹ᵁ U)
    let LY := schemeOpenRestriction Y U
    (LY.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((schemeMVHomotopyOpenComposition h U).hom.app K) ≫
        (schemeMVHomotopyOpenAdjunction Y U).counit.app
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (schemeMVHomotopyOpenRestriction h U).hom.app
          ((RX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((schemeMVHomotopyOpenAdjunction X (h ⁻¹ᵁ U)).counit.app K) := by
  let aX : schemeOpenRestriction X (h ⁻¹ᵁ U) ⊣
      RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom :=
    schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)
  let aY : schemeOpenRestriction Y U ⊣
      RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom :=
    schemeOpenModuleAdjunction Y U
  exact lift_open_counit_square aX aY
    (schemeMVUnderivedOpenRestriction h U) (schemeMVUnderivedOpenComposition h U)
    (schemeMVOrdinaryOpenCounit_square X Y h U) K

end AlgebraicGeometry
