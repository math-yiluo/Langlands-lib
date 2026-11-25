/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact-derived transport from sheaves to constant towers

Source: blueprint chap-Smooth-purity, classes proof (2), and exact-functor
compatibility of Ext with composite and isomorphic functors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w₁ w₂ w₃ w₄ t₁ t₂ t₃ t₄

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] Functor.mapDerivedCategory mapSingleArrow

private theorem mapSingleArrow_comp_iso
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {E : Type u₃} [Category.{v₃} E] [Abelian E]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D] [HasDerivedCategory.{t₃} E]
    [HasExt.{w₁} C] [HasExt.{w₂} D] [HasExt.{w₃} E] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (τ : H ≅ F ⋙ G) {A B : C} (e : Ext.{w₁} A B 1) :
    mapSingleArrow G 1 (mapSingleArrow F 1 e.hom) =
      (DerivedCategory.singleFunctor E 0).map (τ.inv.app A) ≫
        mapSingleArrow H 1 e.hom ≫
        ((DerivedCategory.singleFunctor E 0).map (τ.hom.app B))⟦(1 : ℤ)⟧' := by
  have h := congrArg (fun x : Ext.{w₃} (G.obj (F.obj A)) (G.obj (F.obj B)) 1 ↦
      (show (DerivedCategory.singleFunctor E 0).obj (G.obj (F.obj A)) ⟶
        ((DerivedCategory.singleFunctor E 0).obj (G.obj (F.obj B)))⟦(1 : ℤ)⟧ from x.hom))
    (Ext.mapExactFunctor_mapExactFunctor_of_iso F G H τ e)
  simp only [Ext.mapExactFunctor_hom, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map,
    Int.natCast_one, Category.assoc] at h
  simpa only [mapSingleArrow, Category.assoc] using h

private theorem mapSingleArrow_precomp
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A A' B : C} (a : A' ⟶ A)
    (h : (DerivedCategory.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.singleFunctor C 0).obj B)⟦(1 : ℤ)⟧) :
    mapSingleArrow F 1 ((DerivedCategory.singleFunctor C 0).map a ≫ h) =
      (DerivedCategory.singleFunctor D 0).map (F.map a) ≫ mapSingleArrow F 1 h := by
  simp only [mapSingleArrow, Functor.map_comp, Category.assoc]
  have hn := (F.mapDerivedCategorySingleFunctor 0).inv.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

private theorem mapSingleArrow_postcomp
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A B B' : C} (b : B ⟶ B')
    (h : (DerivedCategory.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.singleFunctor C 0).obj B)⟦(1 : ℤ)⟧) :
    mapSingleArrow F 1 (h ≫ ((DerivedCategory.singleFunctor C 0).map b)⟦(1 : ℤ)⟧') =
      mapSingleArrow F 1 h ≫
        ((DerivedCategory.singleFunctor D 0).map (F.map b))⟦(1 : ℤ)⟧' := by
  simp only [mapSingleArrow, Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]
  have hn := (F.mapDerivedCategorySingleFunctor 0).hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [← Functor.map_comp, hn, Functor.map_comp]

private theorem mapSingleArrow_cancel
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A B : C} {A' B' : D} (z : F.obj A ⟶ A') (a : F.obj B ⟶ B')
    (h : (DerivedCategory.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.singleFunctor C 0).obj B)⟦(1 : ℤ)⟧)
    (h' : (DerivedCategory.singleFunctor D 0).obj A' ⟶
      ((DerivedCategory.singleFunctor D 0).obj B')⟦(1 : ℤ)⟧)
    (hh : mapSingleArrow F 1 h ≫
        ((DerivedCategory.singleFunctor D 0).map a)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor D 0).map z ≫ h') :
    F.mapDerivedCategory.map h ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor C 0).obj B) ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app B)⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor D 0).map a)⟦(1 : ℤ)⟧' =
      (F.mapDerivedCategorySingleFunctor 0).hom.app A ≫
        (DerivedCategory.singleFunctor D 0).map z ≫ h' := by
  apply (cancel_epi ((F.mapDerivedCategorySingleFunctor 0).inv.app A)).1
  simpa only [mapSingleArrow, Category.assoc, Iso.inv_hom_id_app_assoc] using hh

private theorem mapSingleArrow_square_cancel
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {E : Type u₃} [Category.{v₃} E] [Abelian E]
    {H : Type u₄} [Category.{v₄} H] [Abelian H]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    [HasDerivedCategory.{t₃} E] [HasDerivedCategory.{t₄} H]
    [HasExt.{w₁} C] [HasExt.{w₂} D] [HasExt.{w₃} E] [HasExt.{w₄} H]
    [EnoughInjectives C]
    (K : C ⥤ E) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (P : E ⥤ H) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : D ⥤ H) [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    (τ : F ⋙ M ≅ K ⋙ P) {A B : C} {A' B' : D}
    (z : F.obj A ⟶ A') (a : F.obj B ⟶ B')
    (s : P.obj (K.obj A) ⟶ M.obj A') (t : P.obj (K.obj B) ⟶ M.obj B')
    (hs : s = τ.inv.app A ≫ M.map z) (ht : τ.hom.app B ≫ t = M.map a)
    (h : (DerivedCategory.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.singleFunctor C 0).obj B)⟦(1 : ℤ)⟧)
    (h' : (DerivedCategory.singleFunctor D 0).obj A' ⟶
      ((DerivedCategory.singleFunctor D 0).obj B')⟦(1 : ℤ)⟧)
    (hh : mapSingleArrow F 1 h ≫
        ((DerivedCategory.singleFunctor D 0).map a)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor D 0).map z ≫ h') :
    P.mapDerivedCategory.map (mapSingleArrow K 1 h) ≫
        (P.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor E 0).obj (K.obj B)) ≫
        ((P.mapDerivedCategorySingleFunctor 0).hom.app (K.obj B))⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor H 0).map t)⟦(1 : ℤ)⟧' =
      ((P.mapDerivedCategorySingleFunctor 0).hom.app (K.obj A) ≫
        (DerivedCategory.singleFunctor H 0).map s) ≫ mapSingleArrow M 1 h' := by
  let S := DerivedCategory.singleFunctor H 0
  have hh₁ : mapSingleArrow P 1 (mapSingleArrow K 1 h) =
      S.map (τ.inv.app A) ≫ mapSingleArrow M 1 (mapSingleArrow F 1 h) ≫
        (S.map (τ.hom.app B))⟦(1 : ℤ)⟧' := by
    obtain ⟨e, rfl⟩ := (Ext.homEquiv (X := A) (Y := B) (n := 1)).surjective h
    rw [mapSingleArrow_comp_iso K P (F ⋙ M) τ]
    have hc := mapSingleArrow_comp_iso F M (F ⋙ M) (Iso.refl _) e
    simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at hc
    rw [← hc]
  have ht' : (S.map (τ.hom.app B))⟦(1 : ℤ)⟧' ≫ (S.map t)⟦(1 : ℤ)⟧' =
      (S.map (M.map a))⟦(1 : ℤ)⟧' := by
    rw [← Functor.map_comp, ← Functor.map_comp, ht]
  have hn := congrArg (fun k ↦ mapSingleArrow M 1 k) hh
  rw [mapSingleArrow_postcomp, mapSingleArrow_precomp] at hn
  have hsq : mapSingleArrow P 1 (mapSingleArrow K 1 h) ≫
      (S.map t)⟦(1 : ℤ)⟧' = S.map s ≫ mapSingleArrow M 1 h' := by
    rw [hh₁]
    simp only [Category.assoc, ht']
    rw [hn, hs, Functor.map_comp, Category.assoc]
  simpa only [Category.assoc] using
    mapSingleArrow_cancel P s t _ _ hsq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The degree-zero derived endpoint map with its objectwise source type.
Source: exact single comparison (blueprint: lem-sp-constant-tower-derived-square). -/
def derivedSingleEndpoint
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {A : C} {A' : D} (s : P.obj A ⟶ A') :
    P.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj A) ⟶
      (DerivedCategory.singleFunctor D 0).obj A' :=
  (P.mapDerivedCategorySingleFunctor 0).hom.app A ≫
    (DerivedCategory.singleFunctor D 0).map s

/-- The shifted derived endpoint map with its objectwise source type.
Source: exact single and shift comparisons
(blueprint: lem-sp-constant-tower-derived-square). -/
def derivedShiftedSingleEndpoint
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {B : C} {B' : D} (t : P.obj B ⟶ B') :
    P.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj B)⟦(1 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor D 0).obj B')⟦(1 : ℤ)⟧ :=
  (P.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
    ((P.mapDerivedCategorySingleFunctor 0).hom.app B)⟦(1 : ℤ)⟧' ≫
    ((DerivedCategory.singleFunctor D 0).map t)⟦(1 : ℤ)⟧'

/-- Transport a sheaf-level derived square through exact constant towers.
Source: blueprint classes proof (2); exact functoriality of Ext.
(blueprint: lem-sp-constant-tower-derived-square).

Proof: realize the source derived arrow as an Ext class. Exact-functor Ext
compatibility identifies the two paths around the functor square, conjugated by
its specified isomorphism. Naturality under source precomposition and shifted
target postcomposition transports the given endpoint square. The two endpoint
identities identify the conjugated endpoints with s and t. Finally cancel the
inverse single comparison. This gives the displayed single and shift comparisons.
The argument applies to arbitrary source and target objects and does not require
s, t, z or a to be invertible.
-/
theorem constant_tower_derived_square {X Y : Scheme.{u}}
    [hDiagY : HasDerivedCategory.{u + 1} (DiagonalAb Y)]
    [hDiagX : HasDerivedCategory.{u + 1} (DiagonalAb X)]
    [hAbY : HasDerivedCategory.{u + 2} (Ab Y)]
    [hAbX : HasDerivedCategory.{u + 2} (Ab X)]
    (F : DiagonalAb Y ⥤ DiagonalAb X)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : Ab Y ⥤ Ab X)
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (τ : F ⋙ constant X ≅ constant Y ⋙ P)
    {A B : DiagonalAb Y} {A' B' : DiagonalAb X}
    (z : F.obj A ⟶ A') (a : F.obj B ⟶ B')
    (s : P.obj ((constant Y).obj A) ⟶ (constant X).obj A')
    (t : P.obj ((constant Y).obj B) ⟶ (constant X).obj B')
    (hs : s = τ.inv.app A ≫ (constant X).map z)
    (ht : τ.hom.app B ≫ t = (constant X).map a)
    (h : (DerivedCategory.singleFunctor (DiagonalAb Y) 0).obj A ⟶
      ((DerivedCategory.singleFunctor (DiagonalAb Y) 0).obj B)⟦(1 : ℤ)⟧)
    (h' : (DerivedCategory.singleFunctor (DiagonalAb X) 0).obj A' ⟶
      ((DerivedCategory.singleFunctor (DiagonalAb X) 0).obj B')⟦(1 : ℤ)⟧)
    (hh : mapSingleArrow F 1 h ≫
        ((DerivedCategory.singleFunctor (DiagonalAb X) 0).map a)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor (DiagonalAb X) 0).map z ≫ h') :
    P.mapDerivedCategory.map (mapSingleArrow (constant Y) 1 h) ≫
        derivedShiftedSingleEndpoint P t =
      derivedSingleEndpoint P s ≫ mapSingleArrow (constant X) 1 h' := by
  let _ : HasExt.{u + 2} (DiagonalAb Y) := HasExt.standard _
  let _ : HasExt.{u + 2} (DiagonalAb X) := HasExt.standard _
  simpa only [derivedSingleEndpoint, derivedShiftedSingleEndpoint] using
    (mapSingleArrow_square_cancel (constant Y) P F (constant X)
      τ z a s t hs ht h h' hh)

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
