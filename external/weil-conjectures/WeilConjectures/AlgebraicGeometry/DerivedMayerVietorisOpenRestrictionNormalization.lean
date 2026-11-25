/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # Restriction normalization by derived units

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-derived-mayer-vietoris-open-restriction-normalization).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

section

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C : Type u₁} {D : Type u₂} {A : Type u₃} {B : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} A] [Category.{v₄} B]
  [Abelian C] [Abelian D] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [HasDerivedCategory.{w₃} A] [HasDerivedCategory.{w₄} B]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions A]
  (F : C ⥤ D) (G : A ⥤ B) (LX : C ⥤ A) (LY : D ⥤ B)
  [F.Additive] [G.Additive] [LX.Additive] [LY.Additive]
  [PreservesFiniteLimits LX] [PreservesFiniteColimits LX]
  [PreservesFiniteLimits LY] [PreservesFiniteColimits LY]
  [LX.PreservesKInjectiveComplexes]
  (e : F ⋙ LY ≅ LX ⋙ G)
  (K : HomotopyCategory C (ComplexShape.up ℤ))
private theorem restriction_unit_normalization :
    LY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso F LY).symm ≪≫
        Functor.rightDerivedFunctorNatIso e ≪≫
        Functor.rightDerivedFunctorCompIso LX G ≪≫
        Functor.isoWhiskerRight LX.rightDerivedFunctorIsoMapDerivedCategory
          G.rightDerivedFunctor).hom.app (DerivedCategory.Qh.obj K) ≫
      G.rightDerivedFunctor.map (LX.mapDerivedCategoryFactorsh.hom.app K) =
    LY.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (LX ⋙ G))
            (ComplexShape.up ℤ)).symm).hom.app K) ≫
      G.rightDerivedFunctorUnit.app ((LX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  have h₁ := NatTrans.congr_app
    (Functor.rightDerivedNatTrans_fac (F ⋙ LY).rightDerivedFunctor
      (F.rightDerivedFunctor ⋙ LY.rightDerivedFunctor)
      (F ⋙ LY).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F LY)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (𝟙 _)) K
  have h₂ := NatTrans.congr_app
    (Functor.rightDerivedNatTrans_fac (F ⋙ LY).rightDerivedFunctor
      (LX ⋙ G).rightDerivedFunctor
      (F ⋙ LY).rightDerivedFunctorUnit (LX ⋙ G).rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ))
        DerivedCategory.Qh)) K
  have h₃ := NatTrans.congr_app
    (Functor.rightDerivedNatTrans_fac (LX ⋙ G).rightDerivedFunctor
      (LX.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
      (LX ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit LX G)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (𝟙 _)) K
  have h₄ := NatTrans.congr_app LX.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp at h₁ h₂ h₃ h₄
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.assoc]
  have hLY := NatTrans.congr_app LY.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  dsimp at hLY
  have hn := LY.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (F.rightDerivedFunctorUnit.app K)
  dsimp at hn
  have hfirst : (F ⋙ LY).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F LY).hom.app
        (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ LY))
        (ComplexShape.up ℤ)).inv.app K) ≫
      LY.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      LY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) := by
    simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
      Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom]
    erw [Functor.rightDerivedNatTrans_app]
    dsimp [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit]
    simp only [Category.id_comp, Category.comp_id]
  have hfirst' : LY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F LY).inv.app
        (DerivedCategory.Qh.obj K) =
      LY.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ LY))
        (ComplexShape.up ℤ)).hom.app K) ≫
      (F ⋙ LY).rightDerivedFunctorUnit.app K := by
    rw [← cancel_mono ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso F LY).hom.app
      (DerivedCategory.Qh.obj K))]
    simp only [Category.assoc, Iso.inv_hom_id_app, hfirst,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc,
      Category.comp_id]
  rw [reassoc_of% hfirst']
  simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
  rw [reassoc_of% h₂]
  simp only [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom]
  erw [reassoc_of% h₃]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [← G.rightDerivedFunctor.map_comp_assoc, h₄]
  erw [← G.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app,
    G.rightDerivedFunctor.map_id, Category.comp_id]
  have he : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ LY))
      (ComplexShape.up ℤ)).hom.app K ≫
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K =
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K := by
    rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp]
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    rfl
  erw [← DerivedCategory.Qh.map_comp_assoc, he, ← DerivedCategory.Qh.map_comp_assoc]

end

variable (X Y : Scheme.{u}) (h : X ⟶ Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ T : X.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  [∀ T : Y.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  (U : Y.Opens)

attribute [local instance 2000] schemeMVModuleAbelian

/-- The canonical restriction comparison is the derivation of the sectionwise
restriction identification, with its exact-source and exact-target factors.
Source: Stacks Tag 08FE; Tag 0D5T for the composition factors.
Proof: unfold the four factors of schemeMVOpenRestrictionComparison. For the first
factor use the determining equation of rightDerivedFunctorCompMapDerivedCategoryIso;
for the second use rightDerivedNatTrans_fac; for the third use the determining
rightDerivedUnique equation of rightDerivedFunctorCompIso. For the fourth use
rightDerivedFunctorIsoMapDerivedCategory_hom_fac. The intermediate units cancel,
and the mapHomotopyCategory composition factors identify the remaining underived
natural transformation with schemeMVUnderivedOpenRestriction. This proves the
formula for every homotopy object, not only a K-injective one. Empty and full opens
are included because the equation is a factorization of natural transformations.
(blueprint: lem-pc-derived-mayer-vietoris-open-restriction-normalization). -/
theorem schemeMVOpenRestriction_unit_normalization
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
    let G := RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom
    let LX := schemeOpenRestriction X (h ⁻¹ᵁ U)
    let LY := schemeOpenRestriction Y U
    LY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
        (schemeMVOpenRestrictionComparison h U).hom.app (DerivedCategory.Qh.obj K) ≫
        G.rightDerivedFunctor.map (LX.mapDerivedCategoryFactorsh.hom.app K) =
      LY.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((schemeMVHomotopyOpenRestriction h U).hom.app K) ≫
        G.rightDerivedFunctorUnit.app ((LX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
      := by
  classical
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ U)
  let rX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (h ⁻¹ᵁ U)
  let eX := (Scheme.Modules.overEquiv (h ⁻¹ᵁ U)).functor
  have : rX.Additive := Functor.additive_of_preserves_binary_products _
  have : eX.Additive := Functor.additive_of_preserves_binary_products _
  have : (rX ⋙ eX).Additive := Functor.additive_of_preserves_binary_products _
  have : rX.PreservesKInjectiveComplexes :=
    ⟨fun I _ ↦ kInjective_of_restrict_open X.toRingedSpace (h ⁻¹ᵁ U) I⟩
  have : LX.PreservesKInjectiveComplexes := by
    change (rX ⋙ eX).PreservesKInjectiveComplexes
    infer_instance
  exact restriction_unit_normalization
    (RingedSpace.moduleDirectImage h.toLRSHom.toShHom)
    (RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom)
    LX (schemeOpenRestriction Y U) (schemeMVUnderivedOpenRestriction h U) K


end AlgebraicGeometry
