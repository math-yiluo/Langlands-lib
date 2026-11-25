/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
import WeilConjectures.AlgebraicGeometry.DerivedPushforwardSquareMateUnit

/-! # Unit formula for the affine sections mate path

Source: Stacks Project, cohomology.tex, Tags 0D5T and 08HY;
perfect.tex, Tag 0AA7. (blueprint: lem-pc-affine-sections-square-mate-path-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem compUnit_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (H : C ⥤ D) (G : D ⥤ E) [H.Additive] [G.Additive]
    (J : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit H G).app J =
      G.rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj J) ≫
        G.rightDerivedFunctor.map (H.rightDerivedFunctorUnit.app J) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  have hc : (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ G)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) = 𝟙 _ := by
    change (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  erw [hc, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem normalizedCompUnit_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (H : C ⥤ D) (G : D ⥤ E) [H.Additive] [G.Additive]
    {DG : DerivedCategory D ⥤ DerivedCategory E} (a : G.rightDerivedFunctor ≅ DG)
    (J : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit H G).app J ≫
        a.hom.app (H.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) =
      G.rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj J) ≫
        a.hom.app (DerivedCategory.Qh.obj ((H.mapHomotopyCategory (.up ℤ)).obj J)) ≫
          DG.map (H.rightDerivedFunctorUnit.app J) := by
  erw [compUnit_app, Category.assoc, a.hom.naturality]

private theorem comparison_unit_inv
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {RH : C ⥤ D} {DG : D ⥤ E} {DS : C ⥤ E} (b : RH ⋙ DG ≅ DS)
    {L L' : C} {X : D} {Y Z : E}
    (u : X ⟶ RH.obj L) (v : Y ⟶ DG.obj X) (w : Z ⟶ DS.obj L)
    (t : Y ⟶ Z) (ti : Z ⟶ Y) (ht : ti ≫ t = 𝟙 Z)
    (h : v ≫ DG.map u ≫ b.hom.app L = t ≫ w) (x : L ⟶ L') :
    w ≫ DS.map x ≫ b.inv.app L' = ti ≫ v ≫ DG.map (u ≫ RH.map x) := by
  apply (cancel_mono (b.hom.app L')).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.map_comp]
  erw [b.hom.naturality x]
  have hh := congrArg (fun k ↦ ti ≫ k ≫ DS.map x) h
  simpa only [Functor.comp_map, Category.assoc, reassoc_of% ht, Category.id_comp] using
    hh.symm

private theorem comparison_unit_hom
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {RH : C ⥤ D} {DG : D ⥤ E} {DS : C ⥤ E} (b : RH ⋙ DG ≅ DS)
    {L L' : C} {X : D} {Y Z : E}
    (u : X ⟶ RH.obj L) (v : Y ⟶ DG.obj X) (w : Z ⟶ DS.obj L)
    (t : Y ⟶ Z) (h : v ≫ DG.map u ≫ b.hom.app L = t ≫ w) (x : L ⟶ L') :
    v ≫ DG.map (u ≫ RH.map x) ≫ b.hom.app L' = t ≫ w ≫ DS.map x := by
  simp only [Functor.map_comp, Category.assoc]
  erw [b.hom.naturality x]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun k ↦ k ≫ DS.map x) h

-- Exact restriction expands the right-derived uniqueness comparison.
private theorem exactCompUnit_fac
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (H : C ⥤ D) (G : D ⥤ E) [H.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {DH : DerivedCategory C ⥤ DerivedCategory D} (a : H.rightDerivedFunctor ≅ DH)
    (J : HomotopyCategory C (.up ℤ)) :
    (H ⋙ G).rightDerivedFunctorUnit.app J ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso H G ≪≫
        Functor.isoWhiskerRight a G.mapDerivedCategory).hom.app (DerivedCategory.Qh.obj J) =
    G.mapDerivedCategoryFactorsh.inv.app ((H.mapHomotopyCategory (.up ℤ)).obj J) ≫
      G.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app J ≫
        a.hom.app (DerivedCategory.Qh.obj J)) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, ← Category.assoc]
  erw [Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app']
  rw [Functor.map_comp, Category.assoc]

private theorem homotopy_whiskerRight_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {H T : C ⥤ D} [H.Additive] [T.Additive] (e : H ⟶ T)
    (G : D ⥤ E) [G.Additive] (J : HomotopyCategory C (.up ℤ)) :
    ((Functor.whiskerRight e G).mapHomotopyCategory (.up ℤ)).app J =
      (G.mapHomotopyCategory (.up ℤ)).map ((e.mapHomotopyCategory (.up ℤ)).app J) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  rfl

private theorem homotopy_whiskerLeft_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {G T : D ⥤ E} [G.Additive] [T.Additive] (e : G ⟶ T)
    (H : C ⥤ D) [H.Additive] (J : HomotopyCategory C (.up ℤ)) :
    ((Functor.whiskerLeft H e).mapHomotopyCategory (.up ℤ)).app J =
      (e.mapHomotopyCategory (.up ℤ)).app ((H.mapHomotopyCategory (.up ℤ)).obj J) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  rfl

private theorem homotopy_associator_hom_app
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive F]
    (H : C ⥤ D) (G : D ⥤ E) (T : E ⥤ F)
    [H.Additive] [G.Additive] [T.Additive] (J : HomotopyCategory C (.up ℤ)) :
    (((Functor.associator H G T).hom).mapHomotopyCategory (.up ℤ)).app J = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  change (HomotopyCategory.quotient F (.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

private theorem homotopy_associator_inv_app
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive F]
    (H : C ⥤ D) (G : D ⥤ E) (T : E ⥤ F)
    [H.Additive] [G.Additive] [T.Additive] (J : HomotopyCategory C (.up ℤ)) :
    (((Functor.associator H G T).inv).mapHomotopyCategory (.up ℤ)).app J = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  change (HomotopyCategory.quotient F (.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

private theorem restriction_unit_pasting
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions E]
    (H : C ⥤ D) (G : D ⥤ E) (T : C ⥤ E) (ρ : E ⥤ F)
    [H.Additive] [G.Additive] [T.Additive] [ρ.Additive]
    [PreservesFiniteLimits ρ] [PreservesFiniteColimits ρ]
    {DG : DerivedCategory D ⥤ DerivedCategory E}
    {DT : DerivedCategory C ⥤ DerivedCategory E}
    (aG : G.rightDerivedFunctor ≅ DG) (aT : T.rightDerivedFunctor ≅ DT)
    (z : H ⋙ G ≅ T) (d : H.rightDerivedFunctor ⋙ DG ≅ DT)
    (hd : ∀ J : HomotopyCategory C (.up ℤ),
      (Functor.rightDerivedFunctorCompUnit H G).app J ≫
        aG.hom.app (H.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) ≫
        d.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((z.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
        T.rightDerivedFunctorUnit.app J ≫ aT.hom.app (DerivedCategory.Qh.obj J))
    (J : HomotopyCategory C (.up ℤ)) :
    (G ⋙ ρ).rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj J) ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso G ρ ≪≫
        Functor.isoWhiskerRight aG ρ.mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj ((H.mapHomotopyCategory (.up ℤ)).obj J)) ≫
      (DG ⋙ ρ.mapDerivedCategory).map (H.rightDerivedFunctorUnit.app J) ≫
      ρ.mapDerivedCategory.map (d.hom.app (DerivedCategory.Qh.obj J)) =
    DerivedCategory.Qh.map
      (((Functor.isoWhiskerRight z ρ).hom.mapHomotopyCategory (.up ℤ)).app J) ≫
      (T ⋙ ρ).rightDerivedFunctorUnit.app J ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso T ρ ≪≫
        Functor.isoWhiskerRight aT ρ.mapDerivedCategory).hom.app (DerivedCategory.Qh.obj J) := by
  have hG := exactCompUnit_fac G ρ aG ((H.mapHomotopyCategory (.up ℤ)).obj J)
  have hT := exactCompUnit_fac T ρ aT J
  have hz := hd J
  erw [compUnit_app H G J, Category.assoc, aG.hom.naturality_assoc] at hz
  have hf := ρ.mapDerivedCategoryFactorsh.inv.naturality
    ((z.hom.mapHomotopyCategory (.up ℤ)).app J)
  simp only [Functor.comp_map, ← Category.assoc]
  erw [hG]
  simp only [Category.assoc, ← Functor.map_comp]
  erw [hz]
  erw [hT]
  rw [Functor.isoWhiskerRight_hom, homotopy_whiskerRight_app]
  have hh := congrArg (fun k ↦ k ≫ ρ.mapDerivedCategory.map (T.rightDerivedFunctorUnit.app J) ≫
      ρ.mapDerivedCategory.map (aT.hom.app (DerivedCategory.Qh.obj J))) hf.symm
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hh ⊢
  exact hh

-- Generic pasting avoids unfolding scheme scalar actions during naturality calculations.
private theorem sections_unit_pasting
    {C₀ D₀ E₀ F₀cat V₀ W₀ : Type*}
    [Category* C₀] [Category* D₀] [Category* E₀] [Category* F₀cat]
    [Category* V₀] [Category* W₀]
    [Abelian C₀] [Abelian D₀] [Abelian E₀] [Abelian F₀cat]
    [Abelian V₀] [Abelian W₀]
    [HasDerivedCategory C₀] [HasDerivedCategory D₀] [HasDerivedCategory E₀]
    [HasDerivedCategory F₀cat] [HasDerivedCategory V₀] [HasDerivedCategory W₀]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions D₀]
    [Abelian.HasKInjectiveResolutions E₀] [Abelian.HasKInjectiveResolutions F₀cat]
    [Abelian.HasKInjectiveResolutions W₀]
    (P₀ : C₀ ⥤ D₀) (Q₀ : C₀ ⥤ E₀) (F₀ : D₀ ⥤ F₀cat) (G₀ : E₀ ⥤ F₀cat)
    (A₀ : F₀cat ⥤ V₀) (B₀ : E₀ ⥤ W₀) (S₀ : D₀ ⥤ V₀) (T₀ : C₀ ⥤ W₀)
    (ρ₀ : W₀ ⥤ V₀)
    [P₀.Additive] [Q₀.Additive] [F₀.Additive] [G₀.Additive]
    [A₀.Additive] [B₀.Additive] [S₀.Additive] [T₀.Additive] [ρ₀.Additive]
    [PreservesFiniteLimits ρ₀] [PreservesFiniteColimits ρ₀]
    {A : DerivedCategory F₀cat ⥤ DerivedCategory V₀}
    {D : DerivedCategory E₀ ⥤ DerivedCategory W₀}
    {S : DerivedCategory D₀ ⥤ DerivedCategory V₀}
    {T : DerivedCategory C₀ ⥤ DerivedCategory W₀}
    (aA : A₀.rightDerivedFunctor ≅ A) (aB : B₀.rightDerivedFunctor ≅ D)
    (aS : S₀.rightDerivedFunctor ≅ S) (aT : T₀.rightDerivedFunctor ≅ T)
    (t : F₀ ⋙
        A₀ ≅ S₀)
    (b : F₀.rightDerivedFunctor ⋙
        A ≅ S)
    (hb : ∀ J : HomotopyCategory
        D₀ (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (F₀)
          (A₀)).app J ≫
        (aA).hom.app
          ((F₀.rightDerivedFunctor).obj (DerivedCategory.Qh.obj J)) ≫
        b.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((t.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (S₀).rightDerivedFunctorUnit.app J ≫
        (aS).hom.app (DerivedCategory.Qh.obj J))
    (z : Q₀ ⋙
        B₀ ≅ T₀)
    (d : Q₀.rightDerivedFunctor ⋙
        D ≅ T)
    (hd : ∀ J : HomotopyCategory
        C₀ (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (Q₀)
        (B₀)).app J ≫
        (aB).hom.app
          (Q₀.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) ≫
        d.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map
        ((z.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (T₀).rightDerivedFunctorUnit.app J ≫
        (aT).hom.app (DerivedCategory.Qh.obj J))
    (v : G₀ ⋙
        A₀ ≅
      B₀ ⋙
        ρ₀)
    (r : G₀.rightDerivedFunctor ⋙ A ≅
      D ⋙
        (ρ₀).mapDerivedCategory)
    (hr : ∀ J : HomotopyCategory
        E₀ (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (G₀)
          (A₀)).app J ≫
        (aA).hom.app
          ((G₀.rightDerivedFunctor).obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (B₀ ⋙
          ρ₀).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
            (B₀)
            (ρ₀) ≪≫
          Functor.isoWhiskerRight (aB)
            (ρ₀).mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj J))
    (e : P₀ ⋙ F₀ ≅ Q₀ ⋙ G₀)
    (δ : P₀.rightDerivedFunctor ⋙ F₀.rightDerivedFunctor ⟶
      Q₀.rightDerivedFunctor ⋙ G₀.rightDerivedFunctor)
    (hδ : ∀ J : HomotopyCategory C₀ (.up ℤ),
      F₀.rightDerivedFunctorUnit.app ((P₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
        F₀.rightDerivedFunctor.map (P₀.rightDerivedFunctorUnit.app J) ≫
        δ.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((e.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
        G₀.rightDerivedFunctorUnit.app ((Q₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
        G₀.rightDerivedFunctor.map (Q₀.rightDerivedFunctorUnit.app J))
    (J : HomotopyCategory C₀ (.up ℤ)) :
    let α : P₀ ⋙ S₀ ≅ T₀ ⋙ ρ₀ :=
      Functor.isoWhiskerLeft P₀ t.symm ≪≫ (Functor.associator P₀ F₀ A₀).symm ≪≫
        Functor.isoWhiskerRight e A₀ ≪≫ Functor.associator Q₀ G₀ A₀ ≪≫
        Functor.isoWhiskerLeft Q₀ v ≪≫ (Functor.associator Q₀ B₀ ρ₀).symm ≪≫
        Functor.isoWhiskerRight z ρ₀
    (Functor.rightDerivedFunctorCompUnit P₀ S₀).app J ≫
      aS.hom.app (P₀.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) ≫
      b.inv.app (P₀.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) ≫
      A.map (δ.app (DerivedCategory.Qh.obj J)) ≫
      r.hom.app (Q₀.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) ≫
      ρ₀.mapDerivedCategory.map (d.hom.app (DerivedCategory.Qh.obj J)) =
    DerivedCategory.Qh.map ((α.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
      (T₀ ⋙ ρ₀).rightDerivedFunctorUnit.app J ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso T₀ ρ₀ ≪≫
        Functor.isoWhiskerRight aT ρ₀.mapDerivedCategory).hom.app (DerivedCategory.Qh.obj J)
    := by
  intro α
  let P := P₀.rightDerivedFunctor
  let Q := Q₀.rightDerivedFunctor
  let RF := F₀.rightDerivedFunctor
  let RG := G₀.rightDerivedFunctor
  let F := DerivedCategory.Qh.obj J
  let aρ := Functor.rightDerivedFunctorCompMapDerivedCategoryIso T₀ ρ₀ ≪≫
    Functor.isoWhiskerRight aT ρ₀.mapDerivedCategory
  let JP := (P₀.mapHomotopyCategory (.up ℤ)).obj J
  let JQ := (Q₀.mapHomotopyCategory (.up ℤ)).obj J
  let uP := P₀.rightDerivedFunctorUnit.app J
  let uQ := Q₀.rightDerivedFunctorUnit.app J
  let uF := F₀.rightDerivedFunctorUnit.app JP
  let uG := G₀.rightDerivedFunctorUnit.app JQ
  let eJ := (e.hom.mapHomotopyCategory (.up ℤ)).app J
  let nA := A₀.rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh aA.hom
  let aBρ := Functor.rightDerivedFunctorCompMapDerivedCategoryIso B₀ ρ₀ ≪≫
    Functor.isoWhiskerRight aB ρ₀.mapDerivedCategory
  let nBρ := (B₀ ⋙ ρ₀).rightDerivedFunctorUnit ≫
    Functor.whiskerLeft DerivedCategory.Qh aBρ.hom
  let nTρ := (T₀ ⋙ ρ₀).rightDerivedFunctorUnit ≫
    Functor.whiskerLeft DerivedCategory.Qh aρ.hom
  have hb' := hb JP
  erw [compUnit_app F₀ A₀ JP, Category.assoc, aA.hom.naturality_assoc] at hb'
  have hr' := hr JQ
  erw [compUnit_app G₀ A₀ JQ, Category.assoc, aA.hom.naturality_assoc] at hr'
  have hb'' : nA.app ((F₀.mapHomotopyCategory (.up ℤ)).obj JP) ≫
      A.map uF ≫ b.hom.app (DerivedCategory.Qh.obj JP) =
      DerivedCategory.Qh.map ((t.hom.mapHomotopyCategory (.up ℤ)).app JP) ≫
        (S₀.rightDerivedFunctorUnit.app JP ≫ aS.hom.app (DerivedCategory.Qh.obj JP)) := by
    simpa only [nA, uF, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] using hb'
  have hr'' : nA.app ((G₀.mapHomotopyCategory (.up ℤ)).obj JQ) ≫
      A.map uG ≫ r.hom.app (DerivedCategory.Qh.obj JQ) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (.up ℤ)).app JQ) ≫ nBρ.app JQ := by
    simpa only [nA, nBρ, uG, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc] using hr'
  have ht' : DerivedCategory.Qh.map ((t.inv.mapHomotopyCategory (.up ℤ)).app JP) ≫
      DerivedCategory.Qh.map ((t.hom.mapHomotopyCategory (.up ℤ)).app JP) = 𝟙 _ := by
    rw [← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp,
      t.inv_hom_id, NatTrans.mapHomotopyCategory_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
  have hstart : (Functor.rightDerivedFunctorCompUnit P₀ S₀).app J ≫
      aS.hom.app (P.obj F) ≫ b.inv.app (P.obj F) =
      DerivedCategory.Qh.map ((t.inv.mapHomotopyCategory (.up ℤ)).app JP) ≫
        nA.app ((F₀.mapHomotopyCategory (.up ℤ)).obj JP) ≫
        A.map (uF ≫ RF.map uP) := by
    erw [compUnit_app P₀ S₀ J, Category.assoc, aS.hom.naturality_assoc]
    simpa only [P, RF, F, JP, uP, uF, nA, Functor.comp_obj, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc] using
      comparison_unit_inv (RH := RF) (DG := A) (DS := S) b uF
        (nA.app ((F₀.mapHomotopyCategory (.up ℤ)).obj JP))
        (S₀.rightDerivedFunctorUnit.app JP ≫ aS.hom.app (DerivedCategory.Qh.obj JP))
        (DerivedCategory.Qh.map ((t.hom.mapHomotopyCategory (.up ℤ)).app JP))
        (DerivedCategory.Qh.map ((t.inv.mapHomotopyCategory (.up ℤ)).app JP)) ht' hb'' uP
  have hend : nA.app ((G₀.mapHomotopyCategory (.up ℤ)).obj JQ) ≫
      A.map (uG ≫ RG.map uQ) ≫ r.hom.app (Q.obj F) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (.up ℤ)).app JQ) ≫
        nBρ.app JQ ≫ (D ⋙ ρ₀.mapDerivedCategory).map uQ := by
    simpa only [Q, RG, F, JQ, uQ, uG, nA, nBρ, Functor.comp_obj, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc] using
      comparison_unit_hom (RH := RG) (DG := A) (DS := D ⋙ ρ₀.mapDerivedCategory)
        r uG (nA.app ((G₀.mapHomotopyCategory (.up ℤ)).obj JQ)) (nBρ.app JQ)
        (DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (.up ℤ)).app JQ)) hr'' uQ
  have hnA := nA.naturality eJ
  simp only [nA, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map,
    Category.assoc] at hnA
  have htail : nBρ.app JQ ≫ (D ⋙ ρ₀.mapDerivedCategory).map uQ ≫
      ρ₀.mapDerivedCategory.map (d.hom.app F) =
      DerivedCategory.Qh.map
        (((Functor.isoWhiskerRight z ρ₀).hom.mapHomotopyCategory (.up ℤ)).app J) ≫
        nTρ.app J := by
    simpa only [nBρ, nTρ, aBρ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc] using restriction_unit_pasting Q₀ B₀ T₀ ρ₀ aB aT z d hd J
  have hδJ := hδ J
  change uF ≫ RF.map uP ≫ δ.app F = DerivedCategory.Qh.map eJ ≫
    uG ≫ RG.map uQ at hδJ
  have hαJ :
      ((t.inv.mapHomotopyCategory (.up ℤ)).app JP) ≫
        ((A₀.mapHomotopyCategory (.up ℤ)).map eJ) ≫
        ((v.hom.mapHomotopyCategory (.up ℤ)).app JQ) ≫
        (((Functor.isoWhiskerRight z ρ₀).hom.mapHomotopyCategory (.up ℤ)).app J) =
      (α.hom.mapHomotopyCategory (.up ℤ)).app J := by
    simp only [JP, JQ, eJ, α, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app,
      homotopy_whiskerLeft_app, homotopy_whiskerRight_app, homotopy_associator_hom_app,
      homotopy_associator_inv_app, Category.id_comp]
  simp only [nA, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] at hend
  simp only [← Category.assoc] at hαJ
  change _ = DerivedCategory.Qh.map ((α.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
    nTρ.app J
  erw [reassoc_of% hstart]
  erw [Category.assoc]
  erw [← Functor.map_comp_assoc, Category.assoc uF, hδJ]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hnA]
  erw [← A.map_comp_assoc uG (RG.map uQ), reassoc_of% hend, htail]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, hαJ]



variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

private theorem affineBaseChangedSectionsDerivedIso_eq
    {R B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R) :
    affineBaseChangedSectionsDerivedIso f g =
      Functor.rightDerivedFunctorCompMapDerivedCategoryIso
          (affineGlobalSections (pullback.snd f g))
          (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)) ≪≫
        Functor.isoWhiskerRight (affineGlobalSectionsDerivedIso (pullback.snd f g))
          (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory := rfl

-- Keep localization constructions folded while calculating with their API.
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Functor.mapDerivedCategory Functor.rightDerivedFunctorCompUnit
  Functor.rightDerivedFunctorCompMapDerivedCategoryIso
  canonicalPullbackAdjunction affineGlobalSectionsDerivedIso

-- Profiling found expensive linting of the fixed, nondependent forall binders.
set_option linter.all false in
set_option cleanup.letToHave false in
-- The sections and exact-restriction comparisons require unfolding scalar actions.
/-- The path through the square mate and the comparisons r,d, evaluated on the
unit for p_* followed by affine sections. This formula does not involve the derived
comparison c on the other path.
Source: Stacks Project, cohomology.tex, Tags 08HY and 0D5T; perfect.tex, Tag 0AA7.
(blueprint: lem-pc-affine-sections-square-mate-path-unit).
Proof: transpose the fixed pullback composition comparisons under the pinned
composite adjunctions. Their left-derived factorization and the normalized
Hom-equivalence equations identify the resulting mate with the direct-image
composition comparison, compatibly with the pasted right-derived units.
Whisker this unit equation by affine sections. Substitute hb, hr and hd, and
move the direct-image and sections units past the underived comparisons by
naturality. Exact scalar restriction identifies its derived composite unit
with the levelwise restriction comparison. The resulting underived path has
components t^{-1}, the pushforward square comparison, v and z. Each acts as the
identity on sections by ht, hv and hz; their scalar actions agree by the
fibre-product condition. It therefore equals s, by hs and extensionality of
module maps. Deriving this equality gives the displayed localization of s
followed by the sections unit and the exact-restriction comparison. All of
these factorization equations hold on arbitrary homotopy-category objects;
no cancellation of a unit, and no K-injectivity assumption, is used here.
For zero complexes both sides vanish; identity squares reduce to unit coherence. -/
theorem affineSections_square_mate_path_unit
    {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R) :
    let P₀ := RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom
    let Q₀ := RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let G₀ := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let P := schemeDerivedDirectImage (pullback.fst f g)
    let Q := schemeDerivedDirectImage (pullback.snd f g)
    let RF := schemeDerivedDirectImage f
    let RG := schemeDerivedDirectImage g
    let A₀ := affineGlobalSections (𝟙 (Spec R))
    let B₀ := affineGlobalSections (𝟙 (Spec B))
    let S₀ := affineGlobalSections f
    let T₀ := affineGlobalSections (pullback.snd f g)
    let A := affineDerivedGlobalSections (𝟙 (Spec R))
    let D := affineDerivedGlobalSections (𝟙 (Spec B))
    let S := affineDerivedGlobalSections f
    let T := affineDerivedGlobalSections (pullback.snd f g)
    let aA := affineGlobalSectionsDerivedIso (𝟙 (Spec R))
    let aB := affineGlobalSectionsDerivedIso (𝟙 (Spec B))
    let aS := affineGlobalSectionsDerivedIso f
    let aT := affineGlobalSectionsDerivedIso (pullback.snd f g)
    let ρ₀ := ModuleCat.restrictScalars.{u} (affineBaseRingMap g)
    let aρ := affineBaseChangedSectionsDerivedIso f g
    ∀ (t : F₀ ⋙
        A₀ ≅ S₀)
    (b : RF ⋙
        A ≅ S)
    (ht : ∀ (M : SheafOfModules.{u} (moduleRings (X).toRingedSpace))
        (x : (S₀).obj M), (t.hom.app M) x = x)
    (hb : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (X).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (F₀)
          (A₀)).app J ≫
        (aA).hom.app
          ((RF).obj (DerivedCategory.Qh.obj J)) ≫
        b.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((t.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (S₀).rightDerivedFunctorUnit.app J ≫
        (aS).hom.app (DerivedCategory.Qh.obj J))
    (z : Q₀ ⋙
        B₀ ≅ T₀)
    (d : Q ⋙
        D ≅ T)
    (hz : ∀ (M : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : (T₀).obj M), (z.hom.app M) x = x)
    (hd : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (Q₀)
        (B₀)).app J ≫
        (aB).hom.app
          ((Q).obj (DerivedCategory.Qh.obj J)) ≫
        d.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map
        ((z.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (T₀).rightDerivedFunctorUnit.app J ≫
        (aT).hom.app (DerivedCategory.Qh.obj J))
    (v : G₀ ⋙
        A₀ ≅
      B₀ ⋙
        ρ₀)
    (r : RG ⋙ A ≅
      D ⋙
        (ρ₀).mapDerivedCategory)
    (hv : ∀ (M : SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (x : (B₀).obj M), (v.hom.app M) x = x)
    (hr : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (G₀)
          (A₀)).app J ≫
        (aA).hom.app
          ((RG).obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (B₀ ⋙
          ρ₀).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
            (B₀)
            (ρ₀) ≪≫
          Functor.isoWhiskerRight (aB)
            (ρ₀).mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj J))
    (s : P₀ ⋙
        S₀ ≅
      T₀ ⋙
        ρ₀)
    (hs : ∀ (F : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : (T₀).obj F),
      (s.hom.app F) x = x)
    (J : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (.up ℤ)),
    let a := fun {A D : Scheme.{u}} (h : A ⟶ D) ↦ canonicalPullbackAdjunction h
    let p : ∀ {X Y Z : Scheme.{u}} (h : X ⟶ Y) (i : Y ⟶ Z),
        derivedPullback i ⋙ derivedPullback h ≅ derivedPullback (h ≫ i) :=
      @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let k := p (pullback.snd f g) g ≪≫
      eqToIso (congrArg (fun h ↦ derivedPullback h) (pullback.condition (f := f) (g := g)).symm) ≪≫
        (p (pullback.fst f g) f).symm
    let δ := conjugateEquiv ((a f).comp (a (pullback.fst f g)))
      ((a g).comp (a (pullback.snd f g))) k.hom
    let F := DerivedCategory.Qh.obj J
    (Functor.rightDerivedFunctorCompUnit
        (P₀)
        (S₀)).app J ≫
      (aS).hom.app
        ((P).obj F) ≫
      b.inv.app ((P).obj F) ≫
      (A).map (δ.app F) ≫
      r.hom.app ((Q).obj F) ≫
      (ρ₀).mapDerivedCategory.map
        (d.hom.app F) =
    DerivedCategory.Qh.map ((s.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
      (T₀ ⋙
        ρ₀).rightDerivedFunctorUnit.app J ≫
      (aρ).hom.app F := by
  intro P₀ Q₀ F₀ G₀ P Q RF RG A₀ B₀ S₀ T₀ A D S T aA aB aS aT ρ₀ aρ
    t b ht hb z d hz hd v r hv hr s hs J a p k δ
  rw [show aρ = _ from affineBaseChangedSectionsDerivedIso_eq f g]
  -- Elaborate the mate witness before unpacking the existential.
  have hmate := exists_derivedPushforwardSquareMateUnit f g
  obtain ⟨e, he, hδ⟩ := hmate
  let α : P₀ ⋙ S₀ ≅ T₀ ⋙ ρ₀ :=
    Functor.isoWhiskerLeft P₀ t.symm ≪≫ (Functor.associator P₀ F₀ A₀).symm ≪≫
      Functor.isoWhiskerRight e A₀ ≪≫ Functor.associator Q₀ G₀ A₀ ≪≫
      Functor.isoWhiskerLeft Q₀ v ≪≫ (Functor.associator Q₀ B₀ ρ₀).symm ≪≫
      Functor.isoWhiskerRight z ρ₀
  have hti (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (x : S₀.obj M) : (t.inv.app M) x = x := by
    calc
      _ = (t.hom.app M) ((t.inv.app M) x) := (ht M _).symm
      _ = x := by
        have h := congrArg (fun q ↦ q x) (t.inv_hom_id_app M)
        exact h
  have hα : α.hom = s.hom := by
    ext M x
    change (z.hom.app M) ((v.hom.app (Q₀.obj M))
      ((A₀.map (e.hom.app M)) ((t.inv.app (P₀.obj M)) x))) = (s.hom.app M) x
    rw [hti, hv, hz, hs]
    exact he M x
  have h := sections_unit_pasting P₀ Q₀ F₀ G₀ A₀ B₀ S₀ T₀ ρ₀
    aA aB aS aT t b hb z d hd v r hr e δ hδ J
  dsimp (config := { zetaDelta := false }) only at h
  refine h.trans ?_
  exact congrArg (fun τ : P₀ ⋙ S₀ ⟶ T₀ ⋙ ρ₀ ↦
    DerivedCategory.Qh.map ((τ.mapHomotopyCategory (.up ℤ)).app J) ≫
      (T₀ ⋙ ρ₀).rightDerivedFunctorUnit.app J ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso T₀ ρ₀ ≪≫
        Functor.isoWhiskerRight aT ρ₀.mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj J)) hα

end AlgebraicGeometry
