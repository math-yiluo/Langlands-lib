/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-!
# Right derived functors commuting with exact functors, and composition

Let `P : C ⥤ D` and `P' : C' ⥤ D'` be additive functors and `rX : C' ⥤ C`, `rY : D' ⥤ D` exact
functors, `rX` preserving K-injective complexes, with an isomorphism
`e : P' ⋙ rY ≅ rX ⋙ P` (e.g. restriction of scalars commuting with a pushforward). Then the
right derived functors commute with the levelwise functors:
`Functor.rightDerivedFunctorCommIso e : RP' ⋙ D(rY) ≅ D(rX) ⋙ RP`, both sides being right
derived functors of the two isomorphic composites. It is characterized by the units
(`Functor.rightDerivedFunctorCommIso_fac_app`).

These isomorphisms compose (`Functor.rightDerivedFunctorCommIso_hom_app_comp`): given three such
squares `e₁₂`, `e₂₃`, `e₁₃` and isomorphisms `rX₂₃ ⋙ rX₁₂ ≅ rX₁₃`, `rY₂₃ ⋙ rY₁₂ ≅ rY₁₃` such
that `e₁₃` is the composite of `e₁₂` and `e₂₃`, the derived isomorphism of `e₁₃` is the composite
of those of `e₁₂` and `e₂₃`.
-/

@[expose] public section

open CategoryTheory Abelian Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Helpers

variable {V W V' : Type*} [Category* V] [Category* W] [Category* V'] [Preadditive V]
  [Preadditive W] [Preadditive V'] {ι : Type*} (c : ComplexShape ι)

/-- The inverse of the isomorphism `Functor.mapHomotopyCategoryCompIso` attached to
`Iso.refl (F ⋙ G)` is the identity. -/
lemma mapHomotopyCategoryCompIso_refl_inv_app (F : V ⥤ W) (G : W ⥤ V') [F.Additive]
    [G.Additive] (Y : HomotopyCategory V c) :
    (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).inv.app Y = 𝟙 _ := by
  rw [← cancel_epi ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).hom.app Y),
    Iso.hom_inv_id_app, mapHomotopyCategoryCompIso_refl_hom_app]
  exact (Category.comp_id _).symm

end Helpers

section Factorsh

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- The inverse of `Functor.mapDerivedCategoryNatIso e` on the image of an object of the homotopy
category, modulo the factorizations `Functor.mapDerivedCategoryFactorsh`. -/
@[reassoc]
lemma mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_inv_app {F G : C ⥤ D}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    G.mapDerivedCategoryFactorsh.inv.app X ≫
        (mapDerivedCategoryNatIso e).inv.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app X) ≫
        F.mapDerivedCategoryFactorsh.inv.app X := by
  rw [← cancel_mono ((mapDerivedCategoryNatIso e).hom.app _), Category.assoc,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [Category.assoc,
    mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app,
    ← DerivedCategory.Qh.map_comp_assoc, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id,
    NatTrans.id_app, DerivedCategory.Qh.map_id, Category.id_comp]

end Factorsh

section CompMapDerivedCategory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The components of the unit `Functor.rightDerivedFunctorCompMapDerivedCategoryUnit` of
`RF ⋙ D(G)`. -/
lemma rightDerivedFunctorCompMapDerivedCategoryUnit_app_eq
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (rightDerivedFunctorCompMapDerivedCategoryUnit F G).app X =
      DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app X) ≫
        G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app X) := by
  simp [rightDerivedFunctorCompMapDerivedCategoryUnit]

end CompMapDerivedCategory

section CommIso

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C'] [HasDerivedCategory D']
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions C']
  {P : C ⥤ D} {P' : C' ⥤ D'} [P.Additive] [P'.Additive]
  {rX : C' ⥤ C} {rY : D' ⥤ D} [rX.Additive] [rY.Additive]
  [PreservesFiniteLimits rX] [PreservesFiniteColimits rX] [rX.PreservesKInjectiveComplexes]
  [PreservesFiniteLimits rY] [PreservesFiniteColimits rY]

/-- The right derived functors of `P'` and `P` commute with the exact functors `rY` and `rX`:
`RP' ⋙ D(rY) ≅ D(rX) ⋙ RP`, induced by an isomorphism `e : P' ⋙ rY ≅ rX ⋙ P`. -/
noncomputable def rightDerivedFunctorCommIso (e : P' ⋙ rY ≅ rX ⋙ P) :
    P'.rightDerivedFunctor ⋙ rY.mapDerivedCategory ≅
      rX.mapDerivedCategory ⋙ P.rightDerivedFunctor :=
  (rightDerivedFunctorCompMapDerivedCategoryIso P' rY).symm ≪≫ rightDerivedFunctorNatIso e ≪≫
    rightDerivedFunctorCompIso rX P ≪≫
    isoWhiskerRight rX.rightDerivedFunctorIsoMapDerivedCategory P.rightDerivedFunctor

/-- The isomorphism `rightDerivedFunctorCommIso e` is characterized by the units: on the image of
an object `K` of the homotopy category, after the unit of `RP' ⋙ D(rY)`, it is `e` followed by
the unit of `RP` and the comparison for the exact `rX`. -/
@[reassoc]
lemma rightDerivedFunctorCommIso_fac_app (e : P' ⋙ rY ≅ rX ⋙ P)
    (K : HomotopyCategory C' (ComplexShape.up ℤ)) :
    (rightDerivedFunctorCompMapDerivedCategoryUnit P' rY).app K ≫
        (rightDerivedFunctorCommIso e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (rX ⋙ P)) (ComplexShape.up ℤ)).inv.app K) ≫
        P.rightDerivedFunctorUnit.app ((rX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        P.rightDerivedFunctor.map (rX.mapDerivedCategoryFactorsh.inv.app K) := by
  have h₁ : (rightDerivedFunctorCompMapDerivedCategoryUnit P' rY).app K ≫
      (rightDerivedFunctorCompMapDerivedCategoryIso P' rY).inv.app (DerivedCategory.Qh.obj K) =
        (P' ⋙ rY).rightDerivedFunctorUnit.app K := by
    simp [rightDerivedFunctorCompMapDerivedCategoryIso]
  have h₂ : (P' ⋙ rY).rightDerivedFunctorUnit.app K ≫
      (rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) ≫
          (rX ⋙ P).rightDerivedFunctorUnit.app K := by
    simp [rightDerivedFunctorNatIso, rightDerivedFunctorNatTrans]
  have h₃ : (rX ⋙ P).rightDerivedFunctorUnit.app K ≫
      (rightDerivedFunctorCompIso rX P).hom.app (DerivedCategory.Qh.obj K) =
        (rightDerivedFunctorCompUnit rX P).app K := by
    simp [rightDerivedFunctorCompIso]
  have h₄ := NatTrans.congr_app rX.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  simp only [NatTrans.comp_app, whiskerLeft_app] at h₄
  simp only [rightDerivedFunctorCommIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
  simp [rightDerivedFunctorCompUnit, ← Functor.map_comp, h₄]

/-- The characterization `rightDerivedFunctorCommIso_fac_app` with the unit of `RP' ⋙ D(rY)`
written out. -/
@[reassoc]
lemma rightDerivedFunctorCommIso_fac_app' (e : P' ⋙ rY ≅ rX ⋙ P)
    (K : HomotopyCategory C' (ComplexShape.up ℤ)) :
    rY.mapDerivedCategoryFactorsh.inv.app ((P'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        rY.mapDerivedCategory.map (P'.rightDerivedFunctorUnit.app K) ≫
        (rightDerivedFunctorCommIso e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (rX ⋙ P)) (ComplexShape.up ℤ)).inv.app K) ≫
        P.rightDerivedFunctorUnit.app ((rX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        P.rightDerivedFunctor.map (rX.mapDerivedCategoryFactorsh.inv.app K) := by
  have h := rightDerivedFunctorCommIso_fac_app e K
  rw [rightDerivedFunctorCompMapDerivedCategoryUnit_app_eq,
    mapHomotopyCategoryCompIso_refl_inv_app _ P' rY K, DerivedCategory.Qh.map_id, Category.id_comp,
    Category.assoc] at h
  exact h

end CommIso

section Comp

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₁] [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₂] [HasKInjectiveResolutions C₃]
  {P₁ : C₁ ⥤ D₁} {P₂ : C₂ ⥤ D₂} {P₃ : C₃ ⥤ D₃} [P₁.Additive] [P₂.Additive] [P₃.Additive]
  {rX₁₂ : C₂ ⥤ C₁} {rX₂₃ : C₃ ⥤ C₂} {rX₁₃ : C₃ ⥤ C₁}
  [rX₁₂.Additive] [PreservesFiniteLimits rX₁₂] [PreservesFiniteColimits rX₁₂]
  [rX₁₂.PreservesKInjectiveComplexes]
  [rX₂₃.Additive] [PreservesFiniteLimits rX₂₃] [PreservesFiniteColimits rX₂₃]
  [rX₂₃.PreservesKInjectiveComplexes]
  [rX₁₃.Additive] [PreservesFiniteLimits rX₁₃] [PreservesFiniteColimits rX₁₃]
  [rX₁₃.PreservesKInjectiveComplexes]
  {rY₁₂ : D₂ ⥤ D₁} {rY₂₃ : D₃ ⥤ D₂} {rY₁₃ : D₃ ⥤ D₁}
  [rY₁₂.Additive] [PreservesFiniteLimits rY₁₂] [PreservesFiniteColimits rY₁₂]
  [rY₂₃.Additive] [PreservesFiniteLimits rY₂₃] [PreservesFiniteColimits rY₂₃]
  [rY₁₃.Additive] [PreservesFiniteLimits rY₁₃] [PreservesFiniteColimits rY₁₃]

/-- **Composition of the isomorphisms `RP' ⋙ D(rY) ≅ D(rX) ⋙ RP`.** If `e₁₃` is the composite
of `e₁₂` and `e₂₃` up to the composition isomorphisms `cX : rX₂₃ ⋙ rX₁₂ ≅ rX₁₃` and
`cY : rY₂₃ ⋙ rY₁₂ ≅ rY₁₃`, then the derived isomorphism of `e₁₃` is the composite of those of
`e₁₂` and `e₂₃`, up to the induced isomorphisms `D(rX₂₃) ⋙ D(rX₁₂) ≅ D(rX₁₃)` and
`D(rY₂₃) ⋙ D(rY₁₂) ≅ D(rY₁₃)`. -/
theorem rightDerivedFunctorCommIso_hom_app_comp (e₁₂ : P₂ ⋙ rY₁₂ ≅ rX₁₂ ⋙ P₁)
    (e₂₃ : P₃ ⋙ rY₂₃ ≅ rX₂₃ ⋙ P₂) (e₁₃ : P₃ ⋙ rY₁₃ ≅ rX₁₃ ⋙ P₁)
    (cX : rX₂₃ ⋙ rX₁₂ ≅ rX₁₃) (cY : rY₂₃ ⋙ rY₁₂ ≅ rY₁₃)
    (h : ∀ K, e₁₃.hom.app K = cY.inv.app (P₃.obj K) ≫ rY₁₂.map (e₂₃.hom.app K) ≫
      e₁₂.hom.app (rX₂₃.obj K) ≫ P₁.map (cX.hom.app K))
    (K : DerivedCategory C₃) :
    (rightDerivedFunctorCommIso e₁₃).hom.app K =
      (mapDerivedCategoryCompIso rY₂₃ rY₁₂ ≪≫ mapDerivedCategoryNatIso cY).inv.app
          (P₃.rightDerivedFunctor.obj K) ≫
        rY₁₂.mapDerivedCategory.map ((rightDerivedFunctorCommIso e₂₃).hom.app K) ≫
        (rightDerivedFunctorCommIso e₁₂).hom.app (rX₂₃.mapDerivedCategory.obj K) ≫
        P₁.rightDerivedFunctor.map
          ((mapDerivedCategoryCompIso rX₂₃ rX₁₂ ≪≫
            mapDerivedCategoryNatIso cX).hom.app K) := by
  let τ : P₃.rightDerivedFunctor ⋙ rY₁₃.mapDerivedCategory ⟶
      rX₁₃.mapDerivedCategory ⋙ P₁.rightDerivedFunctor :=
    whiskerLeft P₃.rightDerivedFunctor
        (mapDerivedCategoryCompIso rY₂₃ rY₁₂ ≪≫ mapDerivedCategoryNatIso cY).inv ≫
      (associator _ _ _).inv ≫ whiskerRight (rightDerivedFunctorCommIso e₂₃).hom _ ≫
      (associator _ _ _).hom ≫ whiskerLeft _ (rightDerivedFunctorCommIso e₁₂).hom ≫
      (associator _ _ _).inv ≫
      whiskerRight (mapDerivedCategoryCompIso rX₂₃ rX₁₂ ≪≫ mapDerivedCategoryNatIso cX).hom _
  suffices H : (rightDerivedFunctorCommIso e₁₃).hom = τ by
    simpa [τ] using NatTrans.congr_app H K
  refine rightDerived_ext _ (rightDerivedFunctorCompMapDerivedCategoryUnit P₃ rY₁₃)
    (HomotopyCategory.quasiIso C₃ (ComplexShape.up ℤ)) _ _ _ ?_
  ext X
  simp only [NatTrans.comp_app, whiskerLeft_app, τ, Iso.trans_inv, Iso.trans_hom,
    associator_inv_app, associator_hom_app, whiskerRight_app, Category.id_comp,
    Functor.map_comp, Category.assoc]
  rw [rightDerivedFunctorCommIso_fac_app, rightDerivedFunctorCompMapDerivedCategoryUnit_app_eq,
    mapHomotopyCategoryCompIso_refl_inv_app, mapHomotopyCategoryCompIso_refl_inv_app,
    DerivedCategory.Qh.map_id, DerivedCategory.Qh.map_id, Category.id_comp, Category.id_comp,
    Category.assoc]
  erw [(mapDerivedCategoryNatIso cY).inv.naturality_assoc,
    (mapDerivedCategoryCompIso rY₂₃ rY₁₂).inv.naturality_assoc]
  rw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_inv_app_assoc]
  erw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_hom_app_assoc]
  rw [mapHomotopyCategoryCompIso_refl_inv_app, DerivedCategory.Qh.map_id, Category.id_comp,
    Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    rightDerivedFunctorCommIso_fac_app', Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Category.assoc]
  simp only [Category.assoc]
  erw [← NatTrans.naturality_assoc rY₁₂.mapDerivedCategoryFactorsh.inv,
    ← NatTrans.naturality_assoc rY₁₂.mapDerivedCategoryFactorsh.inv]
  rw [← Functor.comp_map R(P₂) D(rY₁₂)]
  have hn := (rightDerivedFunctorCommIso e₁₂).hom.naturality
    (rX₂₃.mapDerivedCategoryFactorsh.inv.app X)
  erw [reassoc_of% hn]
  erw [rightDerivedFunctorCommIso_fac_app'_assoc]
  simp only [← Functor.map_comp]
  erw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_inv_app_assoc]
  rw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app, Functor.map_comp,
    Functor.map_comp]
  erw [← P₁.rightDerivedFunctorUnit.naturality_assoc,
    ← P₁.rightDerivedFunctorUnit.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  congr 2
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [mapHomotopyCategoryCompIso_refl_inv_app, mapHomotopyCategoryCompIso_refl_hom_app,
    Category.comp_id, Category.id_comp]
  erw [Functor.map_id, Category.id_comp]
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
    ← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, h]
  rfl

end Comp

end CategoryTheory.Functor
