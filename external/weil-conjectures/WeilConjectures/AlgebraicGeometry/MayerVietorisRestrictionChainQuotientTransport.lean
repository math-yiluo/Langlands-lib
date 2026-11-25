/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain

/-! # Complex localization of the open restriction square

Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: lem-pc-mayer-vietoris-image-restriction-localization).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

private lemma schemeMV_quotient_factor_inv_map
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Abelian D]
    [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) :
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app I) = 𝟙 _ := by
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  exact DerivedCategory.Qh.map_id _

private lemma schemeMV_exact_restriction_quotient_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (I : CochainComplex C ℤ) :
    L.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj I) ≫
        L.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).hom.app I) =
      (DerivedCategory.quotientCompQhIso _).hom.app
          ((L.mapHomologicalComplex (.up ℤ)).obj I) ≫
        L.mapDerivedCategoryFactors.inv.app I := by
  apply (cancel_epi (L.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient _ _).obj I))).1
  rw [Iso.hom_inv_id_app_assoc, L.mapDerivedCategoryFactorsh_hom_app]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Category.assoc]
  erw [DerivedCategory.Qh.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app, Category.comp_id]

-- Prove the transport algebra without unfolding the exact or derived functors.
private lemma schemeMV_transport_restriction_chain
    {B C D : Type*} [Category B] [Category C] [Category D]
    (L : B ⥤ D) (R : C ⥤ D)
    {B₀ B₁ : B} {C₀ C₁ C₂ C₃ : C} {D₀ D₁ E₀ E₁ : D}
    (ey : B₀ ≅ B₁) (ed : D₀ ≅ D₁) (eu : E₀ ≅ E₁) (ex : C₀ ≅ C₁)
    (y : L.obj B₁ ⟶ D₁) (yh : L.obj B₀ ⟶ D₀)
    (a : D₁ ⟶ E₁) (ah : D₀ ⟶ E₀) (u : E₀ ⟶ R.obj C₀)
    (xi : C₁ ⟶ C₂) (xh : C₀ ⟶ C₃) (t : C₃ ⟶ C₂)
    (hy : yh = L.map ey.hom ≫ y ≫ ed.inv)
    (ha : a ≫ eu.inv = ed.inv ≫ ah) (hx : xh ≫ t = ex.hom ≫ xi) :
    (y ≫ a ≫ (eu.inv ≫ u ≫ R.map ex.hom)) ≫ R.map xi =
      L.map ey.inv ≫ (yh ≫ ah ≫ u) ≫ R.map xh ≫ R.map t := by
  rw [hy]
  simp only [Category.assoc]
  rw [← L.map_comp_assoc, ey.inv_hom_id, L.map_id, Category.id_comp]
  simp only [← Functor.map_comp]
  rw [hx]
  simp only [Functor.map_comp]
  rw [reassoc_of% ha]

private lemma schemeMV_quotient_restriction_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    (F : A ⥤ B) (L : A ⥤ C) (M : B ⥤ D) (G : C ⥤ D)
    [F.Additive] [L.Additive] [M.Additive] [G.Additive]
    (e : F ⋙ M ≅ L ⋙ G) (I : CochainComplex A ℤ) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ G)) (.up ℤ)).symm).hom.app
        ((HomotopyCategory.quotient _ _).obj I) =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) := by
  change (HomotopyCategory.quotient _ _).map
    ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) ≫
      (HomotopyCategory.quotient _ _).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Transport of the explicit four-map restriction chain to the homotopy quotient.
Source: Stacks Project, Tags 08FE and 079V.
Proof: Expand the chain and the transported direct-image unit. Substitute
mapDerivedCategoryFactorsh_hom_app for exact restriction on the quotient.
Use naturality of the quotient comparison on the termwise restriction isomorphism,
and naturality of the restricted direct-image unit on the restriction quotient
factor. The quotient factors cancel in adjacent hom/inverse pairs. The inverse
X-restriction factor is transported by functoriality. This identifies the four-map
complex chain with the homotopy chain; no normalization of the derived restriction
comparison is used. The identity holds also for empty and full opens.
(blueprint: lem-pc-mayer-vietoris-restriction-chain-quotient-transport). -/
theorem schemeMV_restriction_chain_quotient_transport
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
    let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
    let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
    let LY := schemeOpenRestriction Y W
    let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
    schemeMVRestrictionLocalizationChain X Y h W I =
      LY.mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso _).inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I)) ≫
      (LY.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((schemeMVHomotopyOpenRestriction h W).hom.app K) ≫
        G.rightDerivedFunctorUnit.app ((LX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
      G.rightDerivedFunctor.map (LX.mapDerivedCategoryFactorsh.inv.app K) ≫
      G.rightDerivedFunctor.map
        (LX.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).hom.app I)) := by
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
  let LY := schemeOpenRestriction Y W
  have hxi := schemeMV_exact_restriction_quotient_inv LX I
  have hy := LY.mapDerivedCategoryFactorsh_hom_app
    (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)
  have hr := schemeMV_quotient_restriction_app
    (RingedSpace.moduleDirectImage h.toLRSHom.toShHom) LX LY
    (RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom)
    (schemeMVUnderivedOpenRestriction h W) I
  dsimp only
  unfold schemeMVRestrictionLocalizationChain
  simp only [schemeMVDirectImageLocalization, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    schemeMV_quotient_factor_inv_map, Functor.comp_obj, Category.id_comp, Category.comp_id]
  change (schemeMVHomotopyOpenRestriction h W).hom.app
      ((HomotopyCategory.quotient _ _).obj I) = _ at hr
  rw [hr]
  simp only [schemeMV_quotient_factor_inv_map, Functor.comp_obj, Category.comp_id] at hy
  exact schemeMV_transport_restriction_chain LY.mapDerivedCategory
    (RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom).rightDerivedFunctor
    ((DerivedCategory.quotientCompQhIso _).app
      (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj I))
    ((DerivedCategory.quotientCompQhIso _).app
      ((LY.mapHomologicalComplex (.up ℤ)).obj
        (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj I)))
    ((DerivedCategory.quotientCompQhIso _).app
      (((RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj ((LX.mapHomologicalComplex (.up ℤ)).obj I)))
    ((DerivedCategory.quotientCompQhIso _).app ((LX.mapHomologicalComplex (.up ℤ)).obj I))
    _ _ _ _ _ _ _ _ hy
    (DerivedCategory.quotientCompQhIso_inv_naturality
      ((NatTrans.mapHomologicalComplex (schemeMVUnderivedOpenRestriction h W).hom
        (.up ℤ)).app I)) hxi

end AlgebraicGeometry
