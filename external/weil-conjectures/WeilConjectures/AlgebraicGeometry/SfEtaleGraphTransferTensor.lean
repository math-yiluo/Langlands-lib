/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange

-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

/-! # Tensoring the compactification graph transfer

Source: steps 3--4 of `lem-sf-etale-graph-unit-tensor`; Stacks Tag 0GL1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance] Sheaf.monoidalCategory

private theorem ambidextrous_projection
    {C D : Type*} [Category* C] [Category* D]
    {S : D ⥤ C} {H : C ⥤ D} (a : S ⊣ H) (b : H ⊣ S)
    {T : D ⥤ D ⥤ D} {U : C ⥤ C ⥤ C}
    (δ : (Functor.postcompose₂.obj S).obj T ≅
      (((Functor.whiskeringLeft₂ C).obj S).obj S).obj U)
    [IsIso b.unit]
    (hc : ∀ M, a.counit.app M = inv (b.unit.app M))
    (M : C) (N : D)
    [IsIso (((b.projectionMap S U T δ.inv).app M).app N)] :
    ((a.rightAdjointProjectionMap δ.hom).app M).app N =
      inv (((b.projectionMap S U T δ.inv).app M).app N) := by
  let p := ((b.projectionMap S U T δ.inv).app M).app N
  have hp := b.unit_app_comp_map_projectionMap_app_app S U T δ.inv M N
  dsimp at hp
  have he : S.map p ≫ (δ.hom.app (H.obj M)).app N ≫
      (U.map (a.counit.app M)).app (S.obj N) =
      a.counit.app ((U.obj M).obj (S.obj N)) := by
    rw [hc, hc]
    apply (cancel_epi (b.unit.app ((U.obj M).obj (S.obj N)))).mp
    rw [← Category.assoc, ← Category.assoc, hp]
    simp only [Adjunction.projectionMapTranspose, NatTrans.comp_app,
      Functor.whiskeringLeft₂_map_app_app_app_app,
      Functor.whiskeringLeft₂_obj_obj_map_app_app, Category.assoc]
    dsimp only [Functor.id_obj]
    rw [Iso.inv_hom_id_app_app_assoc, ← NatTrans.comp_app, ← Functor.map_comp,
      IsIso.hom_inv_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      IsIso.hom_inv_id]
  apply (a.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_symm_rightAdjointProjectionMap_app_app,
    Adjunction.homEquiv_counit]
  dsimp
  rw [← he]
  dsimp only [p]
  simp only [Functor.map_inv, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

private theorem counit_projection
    {C D : Type*} [Category* C] [Category* D]
    {H : C ⥤ D} {S : D ⥤ C} (b : H ⊣ S)
    {T : D ⥤ D ⥤ D} {U : C ⥤ C ⥤ C}
    (δ : (Functor.postcompose₂.obj S).obj T ≅
      (((Functor.whiskeringLeft₂ C).obj S).obj S).obj U)
    (Y N : D) :
    ((b.projectionMap S U T δ.inv).app (S.obj Y)).app N ≫
        (T.map (b.counit.app Y)).app N =
      H.map ((δ.inv.app Y).app N) ≫ b.counit.app ((T.obj Y).obj N) := by
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.projectionMap_app_app, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  simp only [Adjunction.projectionMapTranspose, NatTrans.comp_app,
    Functor.whiskeringLeft₂_map_app_app_app_app,
    Functor.whiskeringLeft₂_obj_obj_map_app_app, Category.assoc]
  have hn := NatTrans.congr_app (δ.inv.naturality (b.counit.app Y)) N
  dsimp at hn ⊢
  rw [← hn, ← NatTrans.comp_app_assoc, ← U.map_comp, b.right_triangle_components]
  simp only [U.map_id, NatTrans.id_app, Category.id_comp]
  rw [Functor.map_comp, b.unit_naturality_assoc, b.right_triangle_components,
    Category.comp_id]

private theorem open_projection_leftDerived
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j).projectionMap
        L((j)^*[ModuleCat.{u + 1} A])
        (derivedTensor (ModuleCat.{u + 1} A) U)
        (derivedTensor (ModuleCat.{u + 1} A) X)
        (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j).inv =
      derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} A) j := by
  ext M N
  simp only [Adjunction.projectionMap, Adjunction.projectionMapTranspose,
    derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    derivedOpenImmersionLowerShriekProjectionMap, mapDerivedCategoryUpperStarDerivedTensorIso,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.postcompose₂_map_app_app_app,
    Functor.map_comp, Category.assoc]
  rfl

private theorem transfer_tensor
    {C D : Type*} [Category* C] [Category* D]
    {S : D ⥤ C} {H : C ⥤ D} (a : S ⊣ H) (b : H ⊣ S)
    {T : D ⥤ D ⥤ D} {U : C ⥤ C ⥤ C}
    (δ : (Functor.postcompose₂.obj S).obj T ≅
      (((Functor.whiskeringLeft₂ C).obj S).obj S).obj U)
    [IsIso b.unit]
    (hc : ∀ M, a.counit.app M = inv (b.unit.app M))
    (X Y N : D) (ψ : S.obj X ⟶ S.obj Y)
    [IsIso (((b.projectionMap S U T δ.inv).app (S.obj X)).app N)]
    [IsIso (((b.projectionMap S U T δ.inv).app (S.obj Y)).app N)] :
    (T.map (a.unit.app X ≫ H.map ψ ≫ b.counit.app Y)).app N =
      a.unit.app ((T.obj X).obj N) ≫
        H.map ((δ.hom.app X).app N ≫ (U.map ψ).app (S.obj N) ≫
          (δ.inv.app Y).app N) ≫ b.counit.app ((T.obj Y).obj N) := by
  let p := b.projectionMap S U T δ.inv
  have hu := a.unit_app_comp_map_rightAdjointProjectionMap δ.hom X N
  rw [ambidextrous_projection a b δ hc] at hu
  have hn := NatTrans.congr_app (p.naturality ψ) N
  dsimp at hn hu ⊢
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  have he := counit_projection b δ Y N
  dsimp at he
  rw [← he, reassoc_of% hu]
  have hn' := hn
  dsimp only [p] at hn'
  rw [reassoc_of% hn']
  simp only [IsIso.inv_hom_id_assoc]

private theorem identity_tensor
    {C : Type*} [Category* C] [MonoidalCategory C]
    (F : C ⥤ C) (ε : F ≅ 𝟭 C) (c : F ≅ F ⋙ F)
    (δ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (hc : ∀ X, c.hom.app X ≫ F.map (ε.hom.app X) = 𝟙 _)
    (hδ : ∀ X Y, (δ.hom.app X).app Y ≫ (c.hom.app X ⊗ₘ c.hom.app Y) =
      c.hom.app (X ⊗ Y) ≫ F.map ((δ.hom.app X).app Y) ≫
        (δ.hom.app (F.obj X)).app (F.obj Y))
    (X Y : C) :
    (δ.hom.app X).app Y ≫ (ε.hom.app X ⊗ₘ ε.hom.app Y) = ε.hom.app (X ⊗ Y) := by
  have hf := (Functor.FullyFaithful.id C).ofIso ε.symm
  have := hf.faithful
  apply F.map_injective
  apply (cancel_epi (c.hom.app (X ⊗ Y))).mp
  apply (cancel_mono ((δ.hom.app X).app Y)).mp
  have hn : (δ.hom.app (F.obj X)).app (F.obj Y) ≫
      (F.map (ε.hom.app X) ⊗ₘ F.map (ε.hom.app Y)) =
      F.map (ε.hom.app X ⊗ₘ ε.hom.app Y) ≫ (δ.hom.app X).app Y := by
    have hn₁ := NatTrans.congr_app (δ.hom.naturality (ε.hom.app X)) (F.obj Y)
    have hn₂ := (δ.hom.app X).naturality (ε.hom.app Y)
    dsimp at hn₁ hn₂
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def,
      F.map_comp, Category.assoc, ← reassoc_of% hn₁]
    dsimp only [Functor.id_obj]
    rw [← hn₂]
  simp only [F.map_comp, Category.assoc]
  rw [← hn, ← reassoc_of% (hδ X Y), reassoc_of% (hc (X ⊗ Y))]
  simp only [tensorHom_comp_tensorHom, hc, id_tensorHom_id]
  exact Category.comp_id _

private theorem identity_pullback_tensor
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M N : DerivedCategoryModule A X) :
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (𝟙 X) M N).hom ≫
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app M ⊗ₘ
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app N) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app (M ⊗ N) := by
  exact identity_tensor _ (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.comp_id _).symm)
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) (𝟙 X))
    (leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) (𝟙 X))
    (leftDerivedUpperStarTensorComparison_comp (ModuleCat.{u + 1} A)
      (𝟙 X) (𝟙 X) (𝟙 X) (Category.comp_id _).symm) M N

private theorem section_tensor
    (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (s : V ⟶ T) (p : T ⟶ V) (h : s ≫ p = 𝟙 V)
    (M N : DerivedCategoryModule A V) :
    L((s)^*[ModuleCat.{u + 1} A]).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) p M N).hom ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) s
        (L((p)^*[ModuleCat.{u + 1} A]).obj M)
        (L((p)^*[ModuleCat.{u + 1} A]).obj N)).hom ≫
      ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app M ⊗ₘ
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app N) =
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app
        (M ⊗ N) := by
  have hc := leftDerivedUpperStarTensorComparison_comp (ModuleCat.{u + 1} A)
    s p (𝟙 V) h.symm M N
  simp only [← leftDerivedUpperStarTensorIso_hom] at hc
  apply (cancel_epi
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s p (𝟙 V) h.symm).hom.app
      (M ⊗ N))).mp
  simp only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [← reassoc_of% hc]
  simp only [tensorHom_comp_tensorHom, Iso.hom_inv_id_app_assoc]
  exact identity_pullback_tensor A V M N

private theorem open_unit_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategoryModule A U) (N : DerivedCategoryModule A X) :
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j).unit.app
        (M ⊗ L((j)^*[ModuleCat.{u + 1} A]).obj N) ≫
      L((j)^*[ModuleCat.{u + 1} A]).map
        (((derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} A) j).hom.app M).app N) ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j
        (D((j)_!open[ModuleCat.{u + 1} A]).obj M) N).hom =
      ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j).unit.app M ⊗ₘ
        𝟙 (L((j)^*[ModuleCat.{u + 1} A]).obj N)) := by
  have h := (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j)
    |>.unit_app_comp_map_projectionMap_app_app L((j)^*[ModuleCat.{u + 1} A])
      (derivedTensor (ModuleCat.{u + 1} A) U)
      (derivedTensor (ModuleCat.{u + 1} A) X)
      (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j).inv M N
  rw [open_projection_leftDerived A j] at h
  change (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j).unit.app
      (M ⊗ L((j)^*[ModuleCat.{u + 1} A]).obj N) ≫
    L((j)^*[ModuleCat.{u + 1} A]).map
      (((derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} A) j).hom.app M).app N) =
    ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j).unit.app M ▷
      L((j)^*[ModuleCat.{u + 1} A]).obj N) ≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j
      (D((j)_!open[ModuleCat.{u + 1} A]).obj M) N).inv at h
  rw [reassoc_of% h]
  simp only [Iso.inv_hom_id, Category.comp_id, MonoidalCategory.tensorHom_id]

private theorem graph_coefficient
    (A : Type (u + 1)) [CommRing A]
    {V W : Scheme.{u}} (e : V ⟶ W) (c : Compactification e)
    (K : DerivedCategoryModule A W) :
    L((c.selfGraph)^*[ModuleCat.{u + 1} A]).map
        (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A]).map
            ((leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) e).inv.app K) ≫
          (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
            (IsPullback.of_hasPullback c.g e).toCommSq).hom.app K) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        c.selfGraph (pullback.fst c.g e) c.i c.selfGraph_fst.symm).inv.app
        (L((c.g)^*[ModuleCat.{u + 1} A]).obj K) ≫
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app K ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K =
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        c.selfGraph (pullback.snd c.g e) c.selfGraph_snd).hom.app
        (D((e)^*[ModuleCat.{u + 1} A]).obj K) := by
  have h₁ := map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} A) c.selfGraph (pullback.fst c.g e) c.g c.i
      (pullback.fst c.g e ≫ c.g) e c.selfGraph_fst.symm rfl c.comm K
  have h₂ := map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} A) c.selfGraph (pullback.snd c.g e) e (𝟙 V)
      (pullback.fst c.g e ≫ c.g) e c.selfGraph_snd.symm pullback.condition
      (Category.id_comp e).symm K
  have hu := leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A) e K
  have hn := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    c.selfGraph (pullback.snd c.g e) c.selfGraph_snd).hom.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).inv.app K)
  dsimp at hn
  simp only [leftDerivedUpperStarCompactificationIso_eq, derivedSquareUpperStarIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, Iso.hom_inv_id_app_assoc, reassoc_of% h₂]
  have hu' : (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (𝟙 V) e e (Category.id_comp e).symm).inv.app K =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) V).hom.app
        (L((e)^*[ModuleCat.{u + 1} A]).obj K) := by
    apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (𝟙 V) e e (Category.id_comp e).symm).hom.app K)).mp
    simpa only [Iso.hom_inv_id_app] using hu.symm
  rw [hu']
  simp only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app] at hn
  simp only [Category.assoc] at hn
  rw [reassoc_of% hn]
  simp only [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem graph_normalization
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (Q : C ⥤ E) (S : E ⥤ C) (P : D ⥤ E) (I : D ⥤ C) (H : C ⥤ D)
    (α : Q ⋙ S ≅ 𝟭 C) (β : I ≅ P ⋙ S) (η : 𝟭 C ⟶ H ⋙ I)
    (δQ : ∀ M N, Q.obj (M ⊗ N) ≅ Q.obj M ⊗ Q.obj N)
    (δS : ∀ M N, S.obj (M ⊗ N) ≅ S.obj M ⊗ S.obj N)
    (δP : ∀ M N, P.obj (M ⊗ N) ≅ P.obj M ⊗ P.obj N)
    (δI : ∀ M N, I.obj (M ⊗ N) ≅ I.obj M ⊗ I.obj N)
    (hS : ∀ (X : E) {Y Z : E} (f : Y ⟶ Z),
      (δS X Y).inv ≫ S.map (X ◁ f) =
        (S.obj X ◁ S.map f) ≫ (δS X Z).inv)
    (hα : ∀ M N, S.map (δQ M N).hom ≫ (δS (Q.obj M) (Q.obj N)).hom ≫
      (α.hom.app M ⊗ₘ α.hom.app N) = α.hom.app (M ⊗ N))
    (hβ : ∀ M N, S.map (δP M N).hom ≫ (δS (P.obj M) (P.obj N)).hom =
      (β.inv.app (M ⊗ N) ≫ (δI M N).hom) ≫ (β.hom.app M ⊗ₘ β.hom.app N))
    (M J : C) (R : D) (v : Q.obj J ⟶ P.obj R) (τ : I.obj R ≅ J)
    (π : H.obj (M ⊗ I.obj R) ≅ H.obj M ⊗ R)
    (hη : η.app (M ⊗ I.obj R) ≫ I.map π.hom ≫ (δI (H.obj M) R).hom =
      (η.app M ⊗ₘ 𝟙 (I.obj R)))
    (hv : S.map v ≫ β.inv.app R ≫ τ.hom = α.hom.app J) :
    α.hom.app (M ⊗ J) ≫ η.app (M ⊗ J) ≫ β.hom.app (H.obj (M ⊗ J)) =
      S.map (δQ M J).hom ≫ (δS (Q.obj M) (Q.obj J)).hom ≫
        ((α.hom.app M ≫ η.app M ≫ β.hom.app (H.obj M)) ▷ S.obj (Q.obj J)) ≫
        (δS (P.obj (H.obj M)) (Q.obj J)).inv ≫
        S.map ((P.obj (H.obj M) ◁ v) ≫ (δP (H.obj M) R).inv ≫
          P.map (π.inv ≫ H.map (M ◁ τ.hom))) := by
  have hb : (δS (P.obj (H.obj M)) (P.obj R)).inv ≫
      S.map (δP (H.obj M) R).inv =
      (β.inv.app (H.obj M) ⊗ₘ β.inv.app R) ≫
        (δI (H.obj M) R).inv ≫ β.hom.app (H.obj M ⊗ R) := by
    apply (cancel_mono (S.map (δP (H.obj M) R).hom ≫
      (δS (P.obj (H.obj M)) (P.obj R)).hom)).mp
    simp only [Category.assoc]
    rw [hβ]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      tensorHom_comp_tensorHom, Iso.inv_hom_id_app, id_tensorHom_id,
      Iso.inv_hom_id_assoc]
    have hβ' := hβ (H.obj M) R
    simp only [Category.assoc] at hβ'
    rw [← hβ']
    simp only [← S.map_comp_assoc, Iso.inv_hom_id, S.map_id,
      Category.id_comp, Iso.inv_hom_id]
    rfl
  have hu : (η.app M ⊗ₘ 𝟙 (I.obj R)) ≫ (δI (H.obj M) R).inv ≫
      I.map π.inv = η.app (M ⊗ I.obj R) := by
    rw [← hη]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← I.map_comp,
      Iso.hom_inv_id, I.map_id]
    exact Category.comp_id _
  have hv' : S.map v ≫ β.inv.app R = α.hom.app J ≫ τ.inv := by
    apply (cancel_mono τ.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hv
  have ht :
      ((α.hom.app M ≫ η.app M ≫ β.hom.app (H.obj M)) ▷ S.obj (Q.obj J)) ≫
        (S.obj (P.obj (H.obj M)) ◁ S.map v) ≫
        (β.inv.app (H.obj M) ⊗ₘ β.inv.app R) =
      (α.hom.app M ⊗ₘ α.hom.app J) ≫ (M ◁ τ.inv) ≫
        (η.app M ⊗ₘ 𝟙 (I.obj R)) := by
    simp only [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
      tensorHom_comp_tensorHom, Category.assoc, Category.id_comp, Category.comp_id]
    rw [hv']
    simp only [Iso.hom_inv_id_app]
    erw [Category.comp_id]
  symm
  simp only [Functor.map_comp]
  rw [reassoc_of% (hS (P.obj (H.obj M)) v), reassoc_of% hb]
  rw [reassoc_of% ht, reassoc_of% hα]
  have hn := β.hom.naturality π.inv
  dsimp at hn
  rw [← reassoc_of% hn, reassoc_of% hu]
  have hn' := β.hom.naturality (H.map (M ◁ τ.hom))
  dsimp at hn'
  rw [← hn']
  have hnη := η.naturality (M ◁ τ.inv)
  dsimp at hnη
  rw [reassoc_of% hnη]
  simp only [← Functor.map_comp_assoc]
  simp only [← Functor.map_comp, ← MonoidalCategory.whiskerLeft_comp,
    Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id]
  rw [H.map_id, I.map_id, Category.id_comp]

private theorem clopenTransfer_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    {B C : DerivedCategoryModule A X} (N : DerivedCategoryModule A X)
    (ψ : L((j)^*[ModuleCat.{u + 1} A]).obj B ⟶
      L((j)^*[ModuleCat.{u + 1} A]).obj C) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map (clopenTransfer A ψ)).app N =
      clopenTransfer A
        ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j B N).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} A) U).map ψ).app
            (L((j)^*[ModuleCat.{u + 1} A]).obj N) ≫
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j C N).inv) := by
  have hp := open_projection_leftDerived A j
  have hi (M : DerivedCategoryModule A U) :
      IsIso ((((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j).projectionMap
        L((j)^*[ModuleCat.{u + 1} A])
        (derivedTensor (ModuleCat.{u + 1} A) U)
        (derivedTensor (ModuleCat.{u + 1} A) X)
        (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j).inv).app M).app N) := by
    rw [hp]
    infer_instance
  exact transfer_tensor (clopenUpperStarLowerShriekAdjunction A j)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j)
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j)
    (clopenUpperStarLowerShriekAdjunction_counit_app A j) B C N ψ

/-- Pull back the open projection comparison to the self-base-change square.
The second tensor factor is identified by the specified inverse-image square and
exact/left-derived comparison. Source: Stacks Tags 0GL1 and 0E48
(blueprint: lem-sf-etale-graph-transfer-tensor). -/
noncomputable def sfEtaleGraphTensorMap
    (A : Type (u + 1)) [CommRing A]
    {V W : Scheme.{u}} (e : V ⟶ W) (c : Compactification e)
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W) :
    ((derivedTensor (ModuleCat.{u + 1} A) (pullback c.g e)).obj
      (L((pullback.fst c.g e)^*[ModuleCat.{u + 1} A]).obj
        (D((c.i)_!open[ModuleCat.{u + 1} A]).obj M))).obj
      (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A]).obj
        (D((e)^*[ModuleCat.{u + 1} A]).obj K)) ⟶
    L((pullback.fst c.g e)^*[ModuleCat.{u + 1} A]).obj
      (D((c.i)_!open[ModuleCat.{u + 1} A]).obj
        (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K))) :=
  have : IsOpenImmersion c.i := c.isOpenImmersion
  ((derivedTensor (ModuleCat.{u + 1} A) (pullback c.g e)).obj _).map
      (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A]).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).inv.app K) ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g e).toCommSq).hom.app K) ≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.fst c.g e)
      (D((c.i)_!open[ModuleCat.{u + 1} A]).obj M)
      (L((c.g)^*[ModuleCat.{u + 1} A]).obj K)).inv ≫
    L((pullback.fst c.g e)^*[ModuleCat.{u + 1} A]).map
      (((derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} A) c.i).inv.app M).app
          (L((c.g)^*[ModuleCat.{u + 1} A]).obj K) ≫
        D((c.i)_!open[ModuleCat.{u + 1} A]).map
          (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).map
            ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app K ≫
              (leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} A) e).hom.app K)))

/-- The graph isomorphism is monoidal after the section and open projection comparisons.
This is the coherence calculation for pullback composition, the open projection mate, and
exact coefficient change. Source: Stacks Tag 0GL1, blueprint node
`lem-sf-etale-graph-transfer-tensor` step 4. -/
private theorem sfEtaleGraphTransferTensor_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] [IsSeparated e]
    (c : Compactification e)
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W) :
    (compactificationEtaleGraphIso A e c).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K)) =
      L((c.selfGraph)^*[ModuleCat.{u + 1} A]).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
          (pullback.snd c.g e) M (D((e)^*[ModuleCat.{u + 1} A]).obj K)).hom ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) c.selfGraph
        (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A]).obj M)
        (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A]).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K))).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) V).map
        ((compactificationEtaleGraphIso A e c).hom.app M)).app
          (L((c.selfGraph)^*[ModuleCat.{u + 1} A]).obj
            (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A]).obj
              (D((e)^*[ModuleCat.{u + 1} A]).obj K))) ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) c.selfGraph
        ((D((c.i)_!open[ModuleCat.{u + 1} A]) ⋙
          L((pullback.fst c.g e)^*[ModuleCat.{u + 1} A])).obj M)
        (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A]).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K))).inv ≫
      L((c.selfGraph)^*[ModuleCat.{u + 1} A]).map
        (sfEtaleGraphTensorMap A e c M K) := by
  have : IsOpenImmersion c.i := c.isOpenImmersion
  let J := D((e)^*[ModuleCat.{u + 1} A]).obj K
  let R := L((c.g)^*[ModuleCat.{u + 1} A]).obj K
  let α := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    c.selfGraph (pullback.snd c.g e) c.selfGraph_snd
  let β := leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    c.selfGraph (pullback.fst c.g e) c.i c.selfGraph_fst.symm
  let η := (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A c.i).unit
  let v := L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A]).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).inv.app K) ≫
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g e).toCommSq).hom.app K
  let τ := (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).app K ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).app K
  let π := ((derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} A) c.i).app M).app R
  have hS (X : DerivedCategoryModule A (pullback c.g e))
      {Y Z : DerivedCategoryModule A (pullback c.g e)} (f : Y ⟶ Z) :
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) c.selfGraph X Y).inv ≫
        L((c.selfGraph)^*[ModuleCat.{u + 1} A]).map (X ◁ f) =
      (L((c.selfGraph)^*[ModuleCat.{u + 1} A]).obj X ◁
        L((c.selfGraph)^*[ModuleCat.{u + 1} A]).map f) ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) c.selfGraph X Z).inv := by
    apply (cancel_epi
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) c.selfGraph X Y).hom).mp
    apply (cancel_mono
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) c.selfGraph X Z).hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact leftDerivedUpperStarTensorIso_hom_naturality_right c.selfGraph X f
  have hβ (B C : DerivedCategoryModule A c.Z) :
      L((c.selfGraph)^*[ModuleCat.{u + 1} A]).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
          (pullback.fst c.g e) B C).hom ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) c.selfGraph
          (L((pullback.fst c.g e)^*[ModuleCat.{u + 1} A]).obj B)
          (L((pullback.fst c.g e)^*[ModuleCat.{u + 1} A]).obj C)).hom =
      (β.inv.app (B ⊗ C) ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) c.i B C).hom) ≫
        (β.hom.app B ⊗ₘ β.hom.app C) := by
    have hc := leftDerivedUpperStarTensorComparison_comp (ModuleCat.{u + 1} A)
      c.selfGraph (pullback.fst c.g e) c.i c.selfGraph_fst.symm B C
    simp only [← leftDerivedUpperStarTensorIso_hom] at hc
    dsimp only [β]
    rw [Category.assoc, hc, Iso.inv_hom_id_app_assoc]
  have h := graph_normalization
    L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A])
    L((c.selfGraph)^*[ModuleCat.{u + 1} A])
    L((pullback.fst c.g e)^*[ModuleCat.{u + 1} A])
    L((c.i)^*[ModuleCat.{u + 1} A])
    D((c.i)_!open[ModuleCat.{u + 1} A]) α β η
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.snd c.g e))
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) c.selfGraph)
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.fst c.g e))
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) c.i)
    hS (section_tensor A c.selfGraph (pullback.snd c.g e) c.selfGraph_snd) hβ
    M J R v τ π (open_unit_tensor A c.i M R) (graph_coefficient A e c K)
  simpa only [α, β, η, J, R, v, τ, π, compactificationEtaleGraphIso,
    sfEtaleGraphTensorMap, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
    asIso_hom, Iso.symm_hom, Iso.app_inv, Functor.comp_obj,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id, Category.assoc,
    derivedTensor_map_app, derivedTensor_obj_map, derivedTensor,
    curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map] using h

/-- Tensor compatibility of graph transfer, before applying the proper direct image.
Source: `lem-sf-etale-graph-unit-tensor`, steps 2--4; Stacks Tags 015F and 0GL1
(blueprint: lem-sf-etale-graph-transfer-tensor).

Proof in words. The self graph is clopen by the existing graph geometry. For a
clopen immersion, restriction is both left and right adjoint to extension by zero.
The counit of the first adjunction is the inverse unit of the second. Transposing
the tensor projection comparison therefore identifies the two adjoint projection
maps as inverses. Their unit and counit equations and naturality show that tensoring
a transfer is the transfer of the restricted tensor map, with pullback tensor
comparisons inserted. Normalize the graph isomorphism using monoidality of the
section and composition comparisons, the defining open-projection unit equation,
and associativity and identity laws for the coefficient square. Apply transfer to
this normalization and use its naturality at both ends. All calculations use the
specified comparisons. No clopen derived-product construction, boundedness, or
quasi-compactness hypothesis is needed; empty schemes and the zero ring satisfy
the same categorical equations. -/
theorem sfEtaleGraphTransferTensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] [IsSeparated e]
    (c : Compactification e)
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W) :
    (compactificationEtaleGraphMap A e c).app
        (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K)) =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.snd c.g e) M
        (D((e)^*[ModuleCat.{u + 1} A]).obj K)).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) (pullback c.g e)).map
        ((compactificationEtaleGraphMap A e c).app M)).app
          (L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A]).obj
            (D((e)^*[ModuleCat.{u + 1} A]).obj K)) ≫
      sfEtaleGraphTensorMap A e c M K := by
  let J := D((e)^*[ModuleCat.{u + 1} A]).obj K
  let MK := ((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj J
  let μ := (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
    (pullback.snd c.g e) M J).hom
  let N := L((pullback.snd c.g e)^*[ModuleCat.{u + 1} A]).obj J
  let ψ := (compactificationEtaleGraphIso A e c).hom.app M
  let d := sfEtaleGraphTensorMap A e c M K
  have hnorm := sfEtaleGraphTransferTensor_normalization A e c M K
  change clopenTransfer A ((compactificationEtaleGraphIso A e c).hom.app MK) =
    μ ≫ ((derivedTensor (ModuleCat.{u + 1} A) (pullback c.g e)).map
      (clopenTransfer A ψ)).app N ≫ d
  rw [clopenTransfer_tensor A c.selfGraph N ψ]
  rw [← clopenTransfer_comp]
  apply congrArg (clopenTransfer A)
  dsimp only [Functor.comp_obj] at hnorm ⊢
  simpa only [Category.assoc] using hnorm

end AlgebraicGeometry.Etale
