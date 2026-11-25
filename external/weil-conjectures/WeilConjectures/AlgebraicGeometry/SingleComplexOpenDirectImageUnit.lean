/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! # The open direct-image comparison on right-derived units

Source: Stacks Project, Tags 08FE and 08BS.
(blueprint: lem-pc-e2-open-direct-image-unit).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The sectionwise comparison before deriving; this is the explicit comparison
used in `singleComplexOpenDirectImageIso`.
Source: Stacks Project, Tag 08FE.
(blueprint: def-pc-e2-open-underived-direct-image-iso). -/
noncomputable def singleComplexOpenUnderivedDirectImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙ schemeOpenRestriction Y V ≅
      schemeOpenRestriction X (f ⁻¹ᵁ V) ⋙
        RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom := by
  refine Functor.isoWhiskerLeft _ (Scheme.Modules.overFunctorEquiv V) ≪≫
    ?_ ≪≫ Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ V)).symm _
  change Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙ Scheme.Modules.pushforward (f ∣_ V)
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _ ?_ ?_
  · refine NatIso.ofComponents (fun W ↦ eqToIso ?_) ?_
    · exact image_morphismRestrict_preimage f V W
    · cat_disch
  · ext W x
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    dsimp
    exact congr($(morphismRestrict_app f V W.unop) x).symm

/-- The same sectionwise comparison on homotopy categories, including the canonical
composition comparisons for termwise application.
Source: Stacks Project, Tag 08FE.
(blueprint: def-pc-e2-open-homotopy-direct-image-iso). -/
noncomputable def singleComplexOpenHomotopyDirectImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory (.up ℤ) ⋙
        (schemeOpenRestriction Y V).mapHomotopyCategory (.up ℤ) ≅
      (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomotopyCategory (.up ℤ) ⋙
        (RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom).mapHomotopyCategory
          (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso
      (singleComplexOpenUnderivedDirectImageIso f V) (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm

private theorem exact_postcomposition_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (I : HomotopyCategory C (.up ℤ)) :
    (F ⋙ G).rightDerivedFunctorUnit.app I ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F G).hom.app
        (DerivedCategory.Qh.obj I) =
      G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app I) := by
  simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryIso]
  rw [Functor.rightDerivedNatIso_hom]
  erw [Functor.rightDerivedNatTrans_app]
  dsimp [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit]
  simp only [Category.id_comp, Category.comp_id]
  have hi := Iso.hom_inv_id_app
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) I
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at hi
  simp only [hi]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]

private theorem exact_precomposition_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesKInjectiveComplexes] (I : HomotopyCategory C (.up ℤ)) :
    (F ⋙ G).rightDerivedFunctorUnit.app I ≫
      (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj I) ≫
      G.rightDerivedFunctor.map
        (F.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj I)) =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.inv.app I) := by
  have hi := Iso.hom_inv_id_app
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) I
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at hi
  simp only [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom, Functor.rightDerivedNatTrans_app_assoc]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, hi, Category.assoc]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  have hf := congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac I
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  erw [← G.rightDerivedFunctor.map_comp, hf]

private theorem derived_square_unit
    {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    [Abelian C] [Abelian D] [Abelian D'] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory D'] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions D']
    (F : C ⥤ D) (rY : D ⥤ E) (rX : C ⥤ D') (F₀ : D' ⥤ E)
    [F.Additive] [rY.Additive] [rX.Additive] [F₀.Additive]
    [PreservesFiniteLimits rY] [PreservesFiniteColimits rY]
    [PreservesFiniteLimits rX] [PreservesFiniteColimits rX]
    [rX.PreservesKInjectiveComplexes]
    (e : F ⋙ rY ≅ rX ⋙ F₀) (I : HomotopyCategory C (.up ℤ)) :
    let b := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F rY).symm ≪≫
      Functor.rightDerivedFunctorNatIso e ≪≫
      Functor.rightDerivedFunctorCompIso rX F₀ ≪≫
      Functor.isoWhiskerRight rX.rightDerivedFunctorIsoMapDerivedCategory F₀.rightDerivedFunctor
    let eH := Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (rX ⋙ F₀)) (.up ℤ)).symm
    rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
        rY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app I) ≫
        b.hom.app (DerivedCategory.Qh.obj I) =
      DerivedCategory.Qh.map (eH.hom.app I) ≫
        F₀.rightDerivedFunctorUnit.app ((rX.mapHomotopyCategory (.up ℤ)).obj I) ≫
        F₀.rightDerivedFunctor.map (rX.mapDerivedCategoryFactorsh.inv.app I) := by
  dsimp only
  have hY := exact_postcomposition_unit F rY I
  have hX := exact_precomposition_unit rX F₀ I
  have hi := Iso.hom_inv_id_app
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (rX ⋙ F₀)) (.up ℤ)) I
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at hi
  have he : (Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (rX ⋙ F₀)) (.up ℤ)).symm).hom.app I =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app I := by
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
    erw [hi, Category.comp_id]
    rfl
  rw [he]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  erw [← reassoc_of% hY]
  simp only [Iso.hom_inv_id_app_assoc]
  simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    Functor.rightDerivedNatTrans_app_assoc, Functor.whiskerRight_app]
  erw [hX]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluating the constructed derived direct-image comparison on its right-derived
units gives the underived sectionwise comparison on the homotopy category.
Source: Stacks Project, Tags 08FE and 08BS.
(blueprint: lem-pc-e2-open-direct-image-unit).

Proof: Expand the four factors defining the derived comparison. The first factor
is the inverse of right-derived uniqueness for postcomposition by exact restriction;
its unit factorization replaces it with the composite right-derived unit. The second
factor is the right-derived natural isomorphism of the sectionwise comparison, so
its unit factorization gives the image of that comparison under Qh. The third factor
is right-derived composition, whose unit is the composite unit. The last factor
identifies the right-derived exact restriction with its termwise derived functor;
its unit factorization is the inverse of mapDerivedCategoryFactorsh. Reassociate and
use naturality to obtain the displayed equation. No K-injectivity of I is required. -/
theorem singleComplexOpen_directImage_unit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
        rY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app I) ≫
        (singleComplexOpenDirectImageIso f V).hom.app (DerivedCategory.Qh.obj I) =
      DerivedCategory.Qh.map ((singleComplexOpenHomotopyDirectImageIso f V).hom.app I) ≫
        F₀.rightDerivedFunctorUnit.app ((rX.mapHomotopyCategory (.up ℤ)).obj I) ≫
        F₀.rightDerivedFunctor.map (rX.mapDerivedCategoryFactorsh.inv.app I) := by
  classical
  dsimp only
  let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
    RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let F₀ : SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
  let rY := schemeOpenRestriction Y V
  let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
  have : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
      (f ⁻¹ᵁ V)).PreservesKInjectiveComplexes :=
    ⟨fun J _ ↦ kInjective_of_restrict_open X.toRingedSpace (f ⁻¹ᵁ V) J⟩
  let eX := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (f ⁻¹ᵁ V)))
    (D := SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv (f ⁻¹ᵁ V))
  have : eX.Additive := Functor.additive_of_preserves_binary_products _
  have : eX.PreservesKInjectiveComplexes := inferInstance
  have : rX.PreservesKInjectiveComplexes := inferInstance
  exact derived_square_unit F rY rX F₀ (singleComplexOpenUnderivedDirectImageIso f V) I

end AlgebraicGeometry
