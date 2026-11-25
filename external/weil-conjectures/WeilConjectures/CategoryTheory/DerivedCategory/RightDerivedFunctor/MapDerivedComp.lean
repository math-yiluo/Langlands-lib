/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Right derived functors precomposed with an exact functor

Let `L : C ⥤ D` be an exact functor between abelian categories with K-injective resolutions which
preserves K-injective complexes, and let `G : D ⥤ E` be additive. Then `D(L) ⋙ RG`, with the
unit `Functor.mapDerivedCategoryCompRightDerivedFunctorUnit`, is a right derived functor of
`L ⋙ G`, so that `R(L ⋙ G) ≅ D(L) ⋙ RG`
(`Functor.mapDerivedCategoryCompRightDerivedFunctorIso`). Given an isomorphism
`γ : L ⋙ G ≅ H`, this yields `RH ≅ D(L) ⋙ RG`
(`Functor.rightDerivedFunctorIsoMapDerivedCategoryComp`), for instance the invariance of derived
global sections under the pushforward along an isomorphism of schemes.

These isomorphisms compose: for `L₁ : C₁ ⥤ C₂`, `L₂ : C₂ ⥤ C₃` and compatible isomorphisms
`γ₁ : L₁ ⋙ Γ₂ ≅ Γ₁`, `γ₂ : L₂ ⋙ Γ₃ ≅ Γ₂`, `γ₁₂ : L₁₂ ⋙ Γ₃ ≅ Γ₁` with `L₁ ⋙ L₂ ≅ L₁₂`, the
isomorphism for `γ₁₂` is the composite of those for `γ₁` and `γ₂`
(`Functor.rightDerivedFunctorIsoMapDerivedCategoryComp_hom_app_comp`).
-/

@[expose] public section

open CategoryTheory Abelian Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (G : D ⥤ E) [G.Additive]

/-- The unit exhibiting `D(L) ⋙ RG` as a right derived functor of `L ⋙ G`, for an exact
functor `L`: it is assembled from the unit of `RG` and the comparison
`L.mapDerivedCategoryFactorsh`. -/
noncomputable def mapDerivedCategoryCompRightDerivedFunctorUnit :
    (L ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (L.mapDerivedCategory ⋙ G.rightDerivedFunctor) :=
  whiskerRight (mapHomotopyCategoryCompIso (Iso.refl (L ⋙ G)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    (associator _ _ _).hom ≫
    whiskerLeft (L.mapHomotopyCategory (ComplexShape.up ℤ)) G.rightDerivedFunctorUnit ≫
    (associator _ _ _).inv ≫
    whiskerRight L.mapDerivedCategoryFactorsh.inv G.rightDerivedFunctor ≫
    (associator _ _ _).hom

omit [HasKInjectiveResolutions C] in
lemma mapDerivedCategoryCompRightDerivedFunctorUnit_app
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompRightDerivedFunctorUnit L G).app X =
      DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (L ⋙ G)) (ComplexShape.up ℤ)).inv.app X) ≫
        G.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.inv.app X) := by
  simp [mapDerivedCategoryCompRightDerivedFunctorUnit]

variable [L.PreservesKInjectiveComplexes]

/-- If `L` is exact and preserves K-injective complexes, then `D(L) ⋙ RG` is a right derived
functor of `L ⋙ G`: its unit is an isomorphism on K-injective complexes. -/
instance isRightDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor :
    (L.mapDerivedCategory ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor
      (mapDerivedCategoryCompRightDerivedFunctorUnit L G)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  refine (HomotopyCategory.KInjectives.localizerMorphism_derives
    ((L ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X₁
  change IsIso ((mapDerivedCategoryCompRightDerivedFunctorUnit L G).app
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))
  have h₂ : IsIso (G.rightDerivedFunctorUnit.app
      ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))) :=
    inferInstanceAs (IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))))
  have h₃ : IsIso (G.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))) :=
    inferInstanceAs (IsIso (G.rightDerivedFunctor.mapIso
      (L.mapDerivedCategoryFactorsh.app _).symm).hom)
  rw [mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  infer_instance

/-- **Right derived functors precomposed with an exact functor**: `R(L ⋙ G) ≅ D(L) ⋙ RG` for
an exact functor `L` preserving K-injective complexes. -/
noncomputable def mapDerivedCategoryCompRightDerivedFunctorIso :
    (L ⋙ G).rightDerivedFunctor ≅ L.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  rightDerivedUnique (L ⋙ G).rightDerivedFunctor
    (L.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (L ⋙ G).rightDerivedFunctorUnit (mapDerivedCategoryCompRightDerivedFunctorUnit L G)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

@[reassoc]
lemma mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (L ⋙ G).rightDerivedFunctorUnit.app X ≫
        (mapDerivedCategoryCompRightDerivedFunctorIso L G).hom.app (DerivedCategory.Qh.obj X) =
      (mapDerivedCategoryCompRightDerivedFunctorUnit L G).app X := by
  simp [mapDerivedCategoryCompRightDerivedFunctorIso]

variable {L G} {H : C ⥤ E} [H.Additive]

/-- The isomorphism `RH ≅ D(L) ⋙ RG` induced by an isomorphism `γ : L ⋙ G ≅ H`, for an exact
functor `L` preserving K-injective complexes. -/
noncomputable def rightDerivedFunctorIsoMapDerivedCategoryComp (γ : L ⋙ G ≅ H) :
    H.rightDerivedFunctor ≅ L.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (rightDerivedFunctorNatIso γ).symm ≪≫ mapDerivedCategoryCompRightDerivedFunctorIso L G

/-- The isomorphism `rightDerivedFunctorIsoMapDerivedCategoryComp γ` is characterized by the
units: the unit of `RH` followed by it is `γ⁻¹` followed by the unit of `D(L) ⋙ RG`. -/
@[reassoc]
lemma rightDerivedFunctorIsoMapDerivedCategoryComp_hom_fac (γ : L ⋙ G ≅ H)
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    H.rightDerivedFunctorUnit.app X ≫
        (rightDerivedFunctorIsoMapDerivedCategoryComp γ).hom.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory γ.inv (ComplexShape.up ℤ)).app X) ≫
        (mapDerivedCategoryCompRightDerivedFunctorUnit L G).app X := by
  have h := rightDerivedNatTrans_app H.rightDerivedFunctor (L ⋙ G).rightDerivedFunctor
    H.rightDerivedFunctorUnit (L ⋙ G).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (whiskerRight (NatTrans.mapHomotopyCategory γ.inv (ComplexShape.up ℤ)) DerivedCategory.Qh) X
  simp only [rightDerivedFunctorIsoMapDerivedCategoryComp, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, rightDerivedFunctorNatIso, rightDerivedFunctorNatTrans]
  rw [reassoc_of% h, mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app]
  rfl

end

section Factorsh

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

@[reassoc]
lemma mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app {F G : C ⥤ D}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    F.mapDerivedCategoryFactorsh.inv.app X ≫
        (mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app X) ≫
        G.mapDerivedCategoryFactorsh.inv.app X := by
  rw [← cancel_mono (G.mapDerivedCategoryFactorsh.hom.app X), Category.assoc,
    mapDerivedCategoryNatIso_fach, Iso.inv_hom_id_app_assoc, Category.assoc,
    Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

@[reassoc]
lemma mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_hom_app (F : C ⥤ D)
    (G : D ⥤ E) [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (F ⋙ G).mapDerivedCategoryFactorsh.inv.app X ≫
        (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app X) ≫
        G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app X) := by
  have h := mapDerivedCategoryCompIso_fach F G X
  rw [← cancel_epi ((F ⋙ G).mapDerivedCategoryFactorsh.hom.app X), Iso.hom_inv_id_app_assoc,
    ← h]
  simp only [Category.assoc]
  simp [← Functor.map_comp_assoc, ← Functor.map_comp]

@[reassoc]
lemma mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_inv_app (F : C ⥤ D)
    (G : D ⥤ E) [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app X) ≫
        (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app X) ≫
        (F ⋙ G).mapDerivedCategoryFactorsh.inv.app X := by
  have H := mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_hom_app F G X
  rw [← cancel_mono ((mapDerivedCategoryCompIso F G).inv.app _)]
  simp only [Category.assoc, Iso.hom_inv_id_app, H]
  rw [← DerivedCategory.Qh.map_comp_assoc, Iso.hom_inv_id_app, DerivedCategory.Qh.map_id,
    Category.id_comp]
  erw [Category.comp_id]

end Factorsh

section Comp

variable {C₁ C₂ C₃ V : Type*} [Category C₁] [Category C₂] [Category C₃] [Category V]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian V]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃] [HasDerivedCategory V]
  [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₂] [HasKInjectiveResolutions C₃]
  {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {L₁₂ : C₁ ⥤ C₃}
  [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [L₁.PreservesKInjectiveComplexes]
  [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [L₂.PreservesKInjectiveComplexes]
  [L₁₂.Additive] [PreservesFiniteLimits L₁₂] [PreservesFiniteColimits L₁₂]
  [L₁₂.PreservesKInjectiveComplexes]
  {Γ₁ : C₁ ⥤ V} {Γ₂ : C₂ ⥤ V} {Γ₃ : C₃ ⥤ V} [Γ₁.Additive] [Γ₂.Additive] [Γ₃.Additive]

/-- **Composition of the isomorphisms `RΓ₁ ≅ D(L) ⋙ RΓ₂`.** Given compatible isomorphisms
`γ₁ : L₁ ⋙ Γ₂ ≅ Γ₁`, `γ₂ : L₂ ⋙ Γ₃ ≅ Γ₂` and `γ₁₂ : L₁₂ ⋙ Γ₃ ≅ Γ₁`, with `ε : L₁ ⋙ L₂ ≅ L₁₂`,
the isomorphism `RΓ₁ ≅ D(L₁₂) ⋙ RΓ₃` of `γ₁₂` is the composite of those of `γ₁` and `γ₂`,
up to `D(L₁₂) ≅ D(L₁) ⋙ D(L₂)`. -/
lemma rightDerivedFunctorIsoMapDerivedCategoryComp_hom_app_comp (γ₁ : L₁ ⋙ Γ₂ ≅ Γ₁)
    (γ₂ : L₂ ⋙ Γ₃ ≅ Γ₂) (γ₁₂ : L₁₂ ⋙ Γ₃ ≅ Γ₁) (ε : L₁ ⋙ L₂ ≅ L₁₂)
    (h : ∀ X, γ₁₂.hom.app X = Γ₃.map (ε.inv.app X) ≫ γ₂.hom.app (L₁.obj X) ≫ γ₁.hom.app X)
    (K : DerivedCategory C₁) :
    (rightDerivedFunctorIsoMapDerivedCategoryComp γ₁).hom.app K ≫
        (rightDerivedFunctorIsoMapDerivedCategoryComp γ₂).hom.app (L₁.mapDerivedCategory.obj K) =
      (rightDerivedFunctorIsoMapDerivedCategoryComp γ₁₂).hom.app K ≫
        Γ₃.rightDerivedFunctor.map ((mapDerivedCategoryNatIso ε.symm).hom.app K ≫
          (mapDerivedCategoryCompIso L₁ L₂).inv.app K) := by
  suffices H : (rightDerivedFunctorIsoMapDerivedCategoryComp γ₁).hom ≫
      whiskerLeft L₁.mapDerivedCategory (rightDerivedFunctorIsoMapDerivedCategoryComp γ₂).hom =
      (rightDerivedFunctorIsoMapDerivedCategoryComp γ₁₂).hom ≫
        whiskerRight ((mapDerivedCategoryNatIso ε.symm).hom ≫
          (mapDerivedCategoryCompIso L₁ L₂).inv) Γ₃.rightDerivedFunctor from congr_app H K
  refine rightDerived_ext Γ₁.rightDerivedFunctor Γ₁.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) _ _ _ ?_
  ext X
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [rightDerivedFunctorIsoMapDerivedCategoryComp_hom_fac_assoc,
    rightDerivedFunctorIsoMapDerivedCategoryComp_hom_fac_assoc,
    mapDerivedCategoryCompRightDerivedFunctorUnit_app,
    mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  simp only [Category.assoc]
  erw [(rightDerivedFunctorIsoMapDerivedCategoryComp γ₂).hom.naturality]
  rw [rightDerivedFunctorIsoMapDerivedCategoryComp_hom_fac_assoc γ₂,
    mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  simp only [Category.assoc, Functor.comp_map, ← Functor.map_comp]
  rw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app_assoc,
    mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_hom_app]
  simp only [Functor.map_comp]
  erw [← Γ₃.rightDerivedFunctorUnit.naturality_assoc,
    ← Γ₃.rightDerivedFunctorUnit.naturality_assoc]
  simp only [Functor.comp_map, ← DerivedCategory.Qh.map_comp_assoc]
  congr 2
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have c₁ : (mapHomotopyCategoryCompIso (Iso.refl (L₁ ⋙ Γ₂)) (ComplexShape.up ℤ)).inv.app
      ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) = 𝟙 _ := rfl
  have c₂ : (mapHomotopyCategoryCompIso (Iso.refl (L₂ ⋙ Γ₃)) (ComplexShape.up ℤ)).inv.app
      ((L₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) = 𝟙 _ := rfl
  have c₃ : (mapHomotopyCategoryCompIso (Iso.refl (L₁₂ ⋙ Γ₃)) (ComplexShape.up ℤ)).inv.app
      ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) = 𝟙 _ := rfl
  have c₄ : (mapHomotopyCategoryCompIso (Iso.refl (L₁ ⋙ L₂)) (ComplexShape.up ℤ)).inv.app
      ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) = 𝟙 _ := rfl
  erw [c₁, c₂, c₃, c₄, Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id,
    Category.comp_id, NatTrans.mapHomotopyCategory_app, NatTrans.mapHomotopyCategory_app,
    NatTrans.mapHomotopyCategory_app, NatTrans.mapHomotopyCategory_app,
    Functor.mapHomotopyCategory_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  change γ₁.inv.app (K.X n) ≫ γ₂.inv.app (L₁.obj (K.X n)) =
    γ₁₂.inv.app (K.X n) ≫ Γ₃.map (ε.inv.app (K.X n))
  rw [← cancel_epi (γ₁₂.hom.app _), Iso.hom_inv_id_app_assoc, h]
  simp

end Comp

end CategoryTheory.Functor
