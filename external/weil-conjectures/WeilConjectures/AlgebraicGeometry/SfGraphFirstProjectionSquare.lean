/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionStages
import all WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import all WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor
import all WeilConjectures.AlgebraicGeometry.SfExactExchangePasting
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars

/-! # Projection compatibility of the first graph side

Source: `LowerShriekComposition.lean`, eA, and Stacks Tags 0B56, 0GL1 and 0F7B.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem projection_square_of_components
    {C : Type*} [Category C] {S T U V : C}
    (a : S ⟶ T) (b : V ⟶ U) {w w' : T ⟶ U} {c c' : S ⟶ V}
    (hw : w = w') (hc : c = c') (h : a ≫ w' = c' ≫ b) :
    a ≫ w = c ≫ b := by
  rw [hw, hc]
  exact h

private theorem projection_square_assoc
    {C : Type*} [Category C] {S T₀ T₁ U V₀ V : C}
    {a : S ⟶ T₀} {w : T₀ ⟶ T₁} {k : T₁ ⟶ U}
    {c : S ⟶ V₀} {d : V₀ ⟶ V} {b : V ⟶ U}
    (h : a ≫ w ≫ k = c ≫ d ≫ b) :
    a ≫ (w ≫ k) = (c ≫ d) ≫ b := by
  simpa only [Category.assoc] using h

private theorem graph_tensor_paste
    {C D E P Z : Type*}
    [Category C] [Category D] [Category E] [Category P] [Category Z]
    (F : C ⥤ D) (Q : D ⥤ C) (J : C ⥤ E) (B : D ⥤ P)
    (P₀ : P ⥤ E) (G : E ⥤ Z) (R : P ⥤ Z)
    (TC : C ⥤ C) (TD : D ⥤ D) (TE : E ⥤ E) (TP : P ⥤ P) (TZ : Z ⥤ Z)
    (ts : F ⋙ TD ⟶ TC ⋙ F) (tq : Q ⋙ TC ⟶ TD ⋙ Q)
    (tj : J ⋙ TE ⟶ TC ⋙ J) (tb : B ⋙ TP ⟶ TD ⋙ B)
    (tp : P₀ ⋙ TE ⟶ TP ⋙ P₀) (tg : G ⋙ TZ ⟶ TE ⋙ G)
    (tr : R ⋙ TZ ⟶ TP ⋙ R)
    (η : 𝟭 C ≅ F ⋙ Q) (ex : Q ⋙ J ≅ B ⋙ P₀) (β : P₀ ⋙ G ≅ R)
    (hη : ∀ M, TC.map (η.hom.app M) ≫ tq.app (F.obj M) ≫ Q.map (ts.app M) =
      η.hom.app (TC.obj M))
    (hex : ∀ M, TE.map (ex.hom.app M) ≫ tp.app (B.obj M) ≫ P₀.map (tb.app M) =
      tj.app (Q.obj M) ≫ J.map (tq.app M) ≫ ex.hom.app (TD.obj M))
    (hβ : ∀ M, TZ.map (β.hom.app M) ≫ tr.app M =
      tg.app (P₀.obj M) ≫ G.map (tp.app M) ≫ β.hom.app (TP.obj M))
    (side : J ⋙ G ⟶ F ⋙ B ⋙ R)
    (hside : ∀ L, side.app L =
      G.map (J.map (η.hom.app L)) ≫ G.map (ex.hom.app (F.obj L)) ≫
        β.hom.app (B.obj (F.obj L)))
    (M : C) :
    TZ.map (side.app M) ≫
      tr.app (B.obj (F.obj M)) ≫ R.map (tb.app (F.obj M)) ≫
      R.map (B.map (ts.app M)) =
    tg.app (J.obj M) ≫ G.map (tj.app M) ≫
      side.app (TC.obj M) := by
  rw [hside M, hside (TC.obj M)]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hβ (B.obj (F.obj M)))]
  have nβ := β.hom.naturality (tb.app (F.obj M) ≫ B.map (ts.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at nβ
  simp only [Functor.map_comp, Category.assoc] at nβ
  rw [← nβ]
  have ng := tg.naturality (ex.hom.app (F.obj M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at ng
  rw [reassoc_of% ng]
  have hm := congrArg G.map (hex (F.obj M))
  simp only [Functor.map_comp] at hm
  rw [reassoc_of% hm]
  have ne := ex.hom.naturality (ts.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ne
  have neG := congrArg G.map ne
  simp only [Functor.map_comp] at neG
  rw [← reassoc_of% neG]
  have ng' := tg.naturality (J.map (η.hom.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at ng'
  rw [reassoc_of% ng']
  have nj := tj.naturality (η.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at nj
  have njG := congrArg G.map nj
  simp only [Functor.map_comp] at njG
  rw [reassoc_of% njG]
  have he := congrArg (fun v ↦ G.map (J.map v)) (hη M)
  simp only [Functor.map_comp] at he
  rw [reassoc_of% he]

private theorem normalized_identity_projection
    {C : Type*} [Category C] {F R : C ⥤ C} (a : F ⊣ R) (T : C ⥤ C ⥤ C)
    (δ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj T)
    (e : F ≅ 𝟭 C)
    (he : ∀ X Y, e.hom.app ((T.obj X).obj Y) =
      (δ.app X).app Y ≫ (T.map (e.hom.app X)).app (F.obj Y) ≫
        (T.obj X).map (e.hom.app Y))
    (M N : C) :
    (T.map ((conjugateEquiv Adjunction.id a e.hom).app M)).app N ≫
      ((a.rightAdjointProjectionMap δ).app M).app N ≫
      R.map ((T.obj M).map (e.hom.app N)) =
    (conjugateEquiv Adjunction.id a e.hom).app ((T.obj M).obj N) := by
  have h := Adjunction.rightAdjointProjectionMap_conjugate
    (T_C := T) (T_D := T) Adjunction.id (𝟙 T) a δ e.hom
    (fun X Y ↦ by simpa only [NatTrans.id_app, Category.comp_id, Functor.id_obj] using he X Y) M N
  have hid (X Y : C) :
      ((Adjunction.id.rightAdjointProjectionMap (T_C := T) (T_D := T)
        (𝟙 T)).app X).app Y = 𝟙 ((T.obj X).obj Y) := by
    rw [Adjunction.rightAdjointProjectionMap_app_app]
    simp only [NatTrans.id_app, Adjunction.id_counit, Functor.id_obj,
      CategoryTheory.Functor.map_id, Category.id_comp]
    change (Adjunction.id.homEquiv _ _) (𝟙 _) = 𝟙 _
    exact (Adjunction.homEquiv_id Adjunction.id _).trans (by rfl)
  rw [hid] at h
  exact h.trans (Category.id_comp _)

private theorem conjugate_ofNatIsoLeft_identity
    {C : Type*} [Category C] {F F' R : C ⥤ C}
    (a : F ⊣ R) (e : F ≅ F') (d : F' ⟶ 𝟭 C) :
    conjugateEquiv Adjunction.id (a.ofNatIsoLeft e) d =
      conjugateEquiv Adjunction.id a (e.hom ≫ d) := by
  ext M
  have h₁ := unit_conjugateEquiv Adjunction.id (a.ofNatIsoLeft e) d M
  have h₂ := unit_conjugateEquiv Adjunction.id a (e.hom ≫ d) M
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp,
    Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.id_obj, Functor.map_comp, Category.assoc] at h₁ h₂
  exact h₁.trans h₂.symm

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

attribute [local instance] Sheaf.monoidalCategory

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint

attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

private noncomputable def section_tensor_comparison
    (A : Type (u + 1)) [CommRing A]
    {X U : Scheme.{u}} (s : X ⟶ U) (q : U ⟶ X) :
    let B := ModuleCat.{u + 1} A
    let F := (upperStar B q).leftDerivedFunctor ⋙ (upperStar B s).leftDerivedFunctor
    (Functor.postcompose₂.obj F).obj (derivedTensor B X) ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (derivedTensor B X) := by
  let B := ModuleCat.{u + 1} A
  exact (Functor.postcompose₂.obj (upperStar B s).leftDerivedFunctor).map
      (leftDerivedUpperStarTensorComparison B q) ≫
    (((Functor.whiskeringLeft₂ _).obj (upperStar B q).leftDerivedFunctor).obj
      (upperStar B q).leftDerivedFunctor).map (leftDerivedUpperStarTensorComparison B s)

private theorem section_tensor_comparison_app
    (A : Type (u + 1)) [CommRing A]
    {X U : Scheme.{u}} (s : X ⟶ U) (q : U ⟶ X)
    (P Q : DerivedCategoryModule A X) :
    ((section_tensor_comparison A s q).app P).app Q =
      (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.map
        (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) q).app P).app Q) ≫
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) s).app
        ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj P)).app
          ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj Q) := by
  rfl

attribute [local irreducible] section_tensor_comparison

private theorem section_tensor_curried
    (A : Type (u + 1)) [CommRing A]
    {X U : Scheme.{u}} (s : X ⟶ U) (q : U ⟶ X) (hs : s ≫ q = 𝟙 X)
    (P Q : DerivedCategoryModule A X) :
    let B := ModuleCat.{u + 1} A
    let φ := section_tensor_comparison A s q
    let e := leftDerivedUpperStarCompSectionIso B s q hs
    e.hom.app (((derivedTensor B X).obj P).obj Q) =
      (φ.app P).app Q ≫
        ((derivedTensor B X).map (e.hom.app P)).app
          ((upperStar B s).leftDerivedFunctor.obj
            ((upperStar B q).leftDerivedFunctor.obj Q)) ≫
        ((derivedTensor B X).obj P).map (e.hom.app Q) := by
  have h := section_tensor A s q hs P Q
  rw [MonoidalCategory.tensorHom_def] at h
  simpa only [section_tensor_comparison_app, NatTrans.comp_app,
    Functor.postcompose₂_obj_map_app_app,
    Functor.whiskeringLeft₂_obj_obj_map_app_app, Functor.comp_obj,
    leftDerivedUpperStarTensorIso_hom, derivedTensor,
    MonoidalCategory.curriedTensor_obj_obj, MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map, Functor.id_obj, Category.assoc] using h.symm

attribute [local irreducible] derivedTensor upperStar lowerStar openImmersionLowerShriek
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  rightDerivedLowerStarProjectionMap derivedOpenImmersionLowerShriekProjectionIso
  rightDerivedLowerStarIdIso rightDerivedLowerStarCompOfEq leftDerivedUpperStarComp
  leftDerivedUpperStarId sfGraphWordProjection sfCompactProjection
  DerivedCategory instCategoryDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  leftDerivedUpperStarTensorComparison openImmersionLowerShriekLowerStarExchange
  derivedSquareUpperStarIso properStrength openStrength properTwistedStrength
  rightDerivedLowerStarComp projectionMapOfCompactification
  leftDerivedUpperStarCompSectionIso derivedUpperStarLowerStarAdjunction
  mapDerivedUpperStarLowerStarAdjunction

attribute [local implicit_reducible] EtaleGraphPresentation.functor sfGraphFirstPresentation

private theorem derived_identity_conjugate
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom =
      (rightDerivedLowerStarIdIso A X).inv := by
  let B := ModuleCat.{u + 1} A
  have h := congrArg Iso.inv (derived_star_id_conjugate A X)
  change conjugateEquiv Adjunction.id
    (mapDerivedUpperStarLowerStarAdjunction B (𝟙 X))
    (Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
      Functor.mapDerivedCategoryIdIso _).hom = _ at h
  rw [mapDerivedUpperStarLowerStarAdjunction_eq,
    conjugate_ofNatIsoLeft_identity] at h
  have he : (leftDerivedUpperStarIsoMapDerivedCategory B (𝟙 X)).hom ≫
      (Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom = (leftDerivedUpperStarId B X).hom := by
    ext M
    exact (leftDerivedUpperStarId_hom_app B X M).symm
  rw [he] at h
  simpa only [rightDerivedLowerStarIdIso] using h

private theorem section_conjugate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U : Scheme.{u}} (s : X ⟶ U) (q : U ⟶ X) (hs : s ≫ q = 𝟙 X) :
    conjugateEquiv Adjunction.id
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s))
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s q hs).hom =
      ((rightDerivedLowerStarIdIso A X).symm ≪≫
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) s q (𝟙 X) hs).symm).hom := by
  let B := ModuleCat.{u + 1} A
  have hc : conjugateEquiv (derivedUpperStarLowerStarAdjunction B (𝟙 X))
      ((derivedUpperStarLowerStarAdjunction B q).comp
        (derivedUpperStarLowerStarAdjunction B s))
      (leftDerivedUpperStarComp B s q (𝟙 X) hs.symm).inv =
      (rightDerivedLowerStarCompOfEq B s q (𝟙 X) hs).inv := by
    have hcomp (r : X ⟶ X) (hr : s ≫ q = r) :
        (conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction B q).comp
            (derivedUpperStarLowerStarAdjunction B s))
          (derivedUpperStarLowerStarAdjunction B r)
          (leftDerivedUpperStarComp B s q r hr.symm)) =
        rightDerivedLowerStarCompOfEq B s q r hr := by
      subst r
      apply Iso.ext
      rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_leftDerivedUpperStarComp_hom]
      unfold rightDerivedLowerStarCompOfEq rightDerivedLowerStarComp
      rfl
    have h := hcomp (𝟙 X) hs
    exact congrArg Iso.inv h
  rw [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom,
    ← conjugateEquiv_comp Adjunction.id (derivedUpperStarLowerStarAdjunction B (𝟙 X)),
    derived_identity_conjugate, hc]
  rfl

private theorem section_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U : Scheme.{u}} (s : X ⟶ U) (q : U ⟶ X) (hs : s ≫ q = 𝟙 X)
    (W M : DerivedCategoryModule A X) :
    let B := ModuleCat.{u + 1} A
    let V := (upperStar B q).leftDerivedFunctor.obj W
    let v := (leftDerivedUpperStarCompSectionIso B s q hs).hom.app W
    let η := (rightDerivedLowerStarIdIso A X).symm ≪≫
      (rightDerivedLowerStarCompOfEq B s q (𝟙 X) hs).symm
    ((derivedTensor B X).flip.obj W).map (η.hom.app M) ≫
      (properStrength B q W).app ((lowerStar B s).rightDerivedFunctor.obj M) ≫
      (lowerStar B q).rightDerivedFunctor.map ((properTwistedStrength B s V v).app M) =
    η.hom.app (((derivedTensor B X).flip.obj W).obj M) := by
  let φ := section_tensor_comparison A s q
  have h := normalized_identity_projection
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)) (derivedTensor (ModuleCat.{u +
        1} A) X) φ
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s q hs)
    (section_tensor_curried A s q hs) M W
  rw [section_conjugate] at h
  rw [Adjunction.rightAdjointProjectionMap_comp (derivedUpperStarLowerStarAdjunction (ModuleCat.{u +
    1} A) q)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) q)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) s) φ
    (section_tensor_comparison_app A s q)] at h
  simp only [properStrength_app, properTwistedStrength_app,
    Functor.flip_obj_obj, Functor.flip_obj_map, Functor.map_comp]
  unfold rightDerivedLowerStarProjectionMap
  rw [Functor.comp_map, Category.assoc] at h
  exact h

private theorem properStrength_compOfEq
    (A : Type (u + 1)) [CommRing A]
    {U V Y : Scheme.{u}} (p : U ⟶ V) (g : V ⟶ Y) (r : U ⟶ Y)
    (h : p ≫ g = r) (K : DerivedCategoryModule A Y) (N : DerivedCategoryModule A U) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).flip.obj K).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) p g r h).hom.app N) ≫
      (properTwistedStrength (ModuleCat.{u + 1} A) r K
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p g r h.symm).hom.app K)).app N =
    (properStrength (ModuleCat.{u + 1} A) g K).app
        ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj N) ≫
      (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
        ((properStrength (ModuleCat.{u + 1} A) p
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)).app N) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) p g r h).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) U).flip.obj
          ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj
            ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))).obj N) := by
  subst r
  simpa only [rightDerivedLowerStarCompOfEq] using
    properStrength_comp (ModuleCat.{u + 1} A) p g K N

private theorem section_square_pullback
    (A : Type (u + 1)) [CommRing A]
    {X U T C : Scheme.{u}} (s : X ⟶ U) (q : U ⟶ X)
    (b : U ⟶ T) (p : T ⟶ C) (j : X ⟶ C)
    (hs : s ≫ q = 𝟙 X) (sq : CommSq q b j p)
    (hj : j = (s ≫ b) ≫ p) (N : DerivedCategoryModule A C) :
    (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app N) ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s q hs).hom.app
        ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj N) =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s b).inv.app
        ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj N) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (s ≫ b) p j hj).inv.app N := by
  let B := ModuleCat.{u + 1} A
  apply (cancel_epi ((leftDerivedUpperStarComp B (s ≫ b) p j hj).hom.app N ≫
    (leftDerivedUpperStarComp B s b).hom.app
      ((upperStar B p).leftDerivedFunctor.obj N))).mp
  have h₁ := leftDerivedUpperStarComp_assoc'_app B s b p (s ≫ b) (q ≫ j) j
    rfl sq.w hj N
  have h₂ := leftDerivedUpperStarComp_assoc'_app B s q j (𝟙 X) (q ≫ j) j
    hs.symm rfl (Category.id_comp j).symm N
  simp only [B] at *
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, leftDerivedUpperStarCompSectionIso,
    Category.assoc]
  rw [← reassoc_of% h₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% h₂, Iso.hom_inv_id_app_assoc]
  exact leftDerivedUpperStarComp_id_left_hom_app B j N

private theorem section_graph_coefficient
    (A : Type (u + 1)) [CommRing A]
    {X U T C Y : Scheme.{u}} (s : X ⟶ U) (q : U ⟶ X)
    (b : U ⟶ T) (p : T ⟶ C) (j : X ⟶ C) (g : C ⟶ Y)
    (r : T ⟶ Y) (f : X ⟶ Y)
    (hs : s ≫ q = 𝟙 X) (sq : CommSq q b j p)
    (hr : r = p ≫ g) (hf : f = j ≫ g) (hword : f = (s ≫ b) ≫ r)
    (K : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p g r hr).hom.app K)) ≫
      (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)) ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s q hs).hom.app
        ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j g f hf).inv.app K =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s b).inv.app
        ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (s ≫ b) r f hword).inv.app K := by
  let B := ModuleCat.{u + 1} A
  have hj : j = (s ≫ b) ≫ p := by
    rw [Category.assoc, ← sq.w, ← Category.assoc, hs, Category.id_comp]
  rw [reassoc_of% (section_square_pullback A s q b p j hs sq hj
    ((upperStar B g).leftDerivedFunctor.obj K))]
  have hn := (leftDerivedUpperStarComp B s b).inv.naturality
    ((leftDerivedUpperStarComp B p g r hr).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  rw [map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app_assoc
    B (s ≫ b) p g j r f hj hr hf, Iso.hom_inv_id_app, Category.comp_id]

private theorem word_strength_transport
    (A : Type (u + 1)) [CommRing A]
    {X U T Y : Scheme.{u}} (s : X ⟶ U) (b : U ⟶ T) (r : T ⟶ Y)
    [IsOpenImmersion b]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y)
    (P : DerivedCategoryModule A T) (Q : DerivedCategoryModule A U)
    (W : DerivedCategoryModule A X)
    (α : (upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K ⟶ P)
    (γ : (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj P ⟶ Q)
    (v : (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.obj Q ⟶ W) :
    let B := ModuleCat.{u + 1} A
    let S := (lowerStar B s).rightDerivedFunctor
    let J := (openImmersionLowerShriek B b).mapDerivedCategory
    let R := (lowerStar B r).rightDerivedFunctor
    (properTwistedStrength B r K α).app (J.obj (S.obj M)) ≫
      R.map ((openStrength B b P γ).app (S.obj M)) ≫
      R.map (J.map ((properTwistedStrength B s Q v).app M)) =
    ((rightDerivedLowerStarProjectionMap B r).app (J.obj (S.obj M))).app K ≫
      R.map (((derivedOpenImmersionLowerShriekProjectionIso B b).inv.app
        (S.obj M)).app ((upperStar B r).leftDerivedFunctor.obj K)) ≫
      R.map (J.map (((rightDerivedLowerStarProjectionMap B s).app M).app
        ((upperStar B b).leftDerivedFunctor.obj
          ((upperStar B r).leftDerivedFunctor.obj K)))) ≫
      R.map (J.map (S.map (((derivedTensor B X).obj M).map
        ((upperStar B s).leftDerivedFunctor.map
          ((upperStar B b).leftDerivedFunctor.map α ≫ γ) ≫ v)))) := by
  have hb := congrArg ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor).map
    (openProjection_naturality_right (ModuleCat.{u + 1} A) b (((lowerStar (ModuleCat.{u + 1} A)
      s).rightDerivedFunctor).obj M) _ _ α)
  have hs := congrArg (fun z ↦ ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor).map
    (((openImmersionLowerShriek (ModuleCat.{u + 1} A) b).mapDerivedCategory).map z))
    (properProjection_naturality_right (ModuleCat.{u + 1} A) s M _ _
      ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map α ≫ γ))
  simp only [Functor.map_comp, Category.assoc] at hb hs
  simp only [properTwistedStrength_app, openStrength_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hb, reassoc_of% hs]

-- Separate the successive projections from the final coefficient compositor.
private noncomputable def word_projection_raw
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((t.functor A).obj M)).obj K ⟶
      (t.functor A).obj (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) t.a).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) t.e).leftDerivedFunctor.obj
            ((upperStar (ModuleCat.{u + 1} A) t.p).leftDerivedFunctor.obj K)))) :=
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) t.p).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) t.e).mapDerivedCategory.obj
          ((lowerStar (ModuleCat.{u + 1} A) t.a).rightDerivedFunctor.obj M))).app K ≫
      (lowerStar (ModuleCat.{u + 1} A) t.p).rightDerivedFunctor.map
        (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) t.e).inv.app
          ((lowerStar (ModuleCat.{u + 1} A) t.a).rightDerivedFunctor.obj M)).app
            ((upperStar (ModuleCat.{u + 1} A) t.p).leftDerivedFunctor.obj K)) ≫
      (lowerStar (ModuleCat.{u + 1} A) t.p).rightDerivedFunctor.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) t.e).mapDerivedCategory.map
          (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) t.a).app M).app
            ((upperStar (ModuleCat.{u + 1} A) t.e).leftDerivedFunctor.obj
              ((upperStar (ModuleCat.{u + 1} A) t.p).leftDerivedFunctor.obj K))))

private noncomputable def word_projection_map
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((t.functor A).obj M)).obj K ⟶
      (t.functor A).obj (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) :=
  word_projection_raw A t M K ≫
      (t.functor A).map (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) t.a t.e).inv.app
            ((upperStar (ModuleCat.{u + 1} A) t.p).leftDerivedFunctor.obj K) ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (t.a ≫ t.e) t.p f
            ((Category.assoc _ _ _).trans t.fac).symm).inv.app K))

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem word_projection_components
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    sfGraphWordProjection A t M K = word_projection_map A t M K := by
  simp only [word_projection_map, word_projection_raw, sfGraphWordProjection]
  first
  | (unfold sfGraphProjectionWord
     simp only [Functor.map_comp, EtaleGraphPresentation.functor,
       Functor.comp_map, Functor.comp_obj, Category.assoc])
  | simp only [Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.map_comp, EtaleGraphPresentation.functor, Functor.comp_map,
      Functor.comp_obj, Category.id_comp, Category.assoc]

-- The proper/open projection before applying the coefficient compositor.
private noncomputable def compact_projection_raw
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj K ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) c.i).leftDerivedFunctor.obj
            ((upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K))) :=
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) c.g).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)).app K ≫
      (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
        (((derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} A) c.i).inv.app M).app
            ((upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K))

private noncomputable def compact_projection_map
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj K ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) :=
  compact_projection_raw A c M K ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) c.i c.g f c.comm).inv.app K))

private theorem compact_projection_components
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    sfCompactProjection A c M K = compact_projection_map A c M K := by
  simpa only [sfCompactProjection, compact_projection_map, compact_projection_raw, Category.assoc]
    using
    projectionMapOfCompactification_explicit (ModuleCat.{u + 1} A) c M K

attribute [local irreducible] word_projection_raw compact_projection_raw
  word_projection_map compact_projection_map

private theorem first_side_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (t : EtaleGraphPresentation f)
    (hs : (sfGraphFirstPresentation c t).a ≫
      pullback.snd (pullback.snd t.p c.g) c.i = 𝟙 X)
    (L : DerivedCategoryModule A X) :
    (sfGraphFirstSideIso c t A).hom.app L =
      (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map
          ((rightDerivedLowerStarIdIso A X).inv.app L)) ≫
      (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map
          ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
            (sfGraphFirstPresentation c t).a
            (pullback.snd (pullback.snd t.p c.g) c.i) (𝟙 X) hs).inv.app L)) ≫
      (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
        ((openImmersionLowerShriekLowerStarExchangeIso A
          (IsPullback.of_hasPullback (pullback.snd t.p c.g) c.i).flip).hom.app
            ((lowerStar (ModuleCat.{u + 1} A)
              (sfGraphFirstPresentation c t).a).rightDerivedFunctor.obj L)) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (pullback.snd t.p c.g) c.g (sfGraphFirstPresentation c t).p
        pullback.condition.symm).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
            (sfGraphFirstPresentation c t).e).mapDerivedCategory.obj
              ((lowerStar (ModuleCat.{u + 1} A)
                (sfGraphFirstPresentation c t).a).rightDerivedFunctor.obj L)) := by
  simp only [sfGraphFirstSideIso, locallyClosedGraphSide₁, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Functor.comp_obj, Category.id_comp,
    Functor.map_comp, Category.assoc, sfGraphFirstPresentation]

/-- Projection compatibility of the first graph side.

Source: `LowerShriekComposition.lean`, eA; the tensor calculation uses Stacks
Tags 0B56, 0GL1 and 0F7B (auxiliary; not a blueprint node).

Proof in words. Expand B1 into the inverse direct-image identity comparison, inverse composition
for s1 followed by its retraction q1, the Cartesian proper/open exchange for
O1 = (P x_Y C) x_C X, and the direct-image compositor over Y. The projection
for the identity, transported by the canonical identity pullback and direct-image
comparisons, is the identity tensor map: transpose under the identity adjunction.
For the inverse compositor s1 q1 = id, use the proper projection composition
identity and cancel the compositor components, without inverting a projection.
Apply the proper/open tensor square to q1, the first supporting open, and p2,
whiskered by Rs1. Apply the proper projection composition identity to p2 and c.g.
Naturality moves these squares past one another. Pullback-composition coherence
identifies the coefficient path with the comparison in sfGraphWordProjection of
the first presentation: both are the canonical compositor for s1 b1 p1 p = f.
This gives the displayed equality of arrows; the only extra identity-direct-image
factor cancels with its inverse. No qc or boundedness assumption is used.
-/
theorem sfGraphFirstSideIso_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((sfGraphFirstSideIso c t A).hom.app M)).app K ≫
      sfGraphWordProjection A (sfGraphFirstPresentation c t) M K =
    sfCompactProjection A c M K ≫
      (sfGraphFirstSideIso c t A).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K))  := by
  -- Work with typed component maps throughout the pasting calculation.
  refine projection_square_of_components _ _
    (word_projection_components A (sfGraphFirstPresentation c t) M K)
    (compact_projection_components A c M K) ?_
  unfold word_projection_map compact_projection_map
  let p : (sfGraphFirstPresentation c t).P ⟶ c.Z := pullback.snd t.p c.g
  let q : (sfGraphFirstPresentation c t).U ⟶ X := pullback.snd p c.i
  have hs : ((sfGraphFirstPresentation c t).a) ≫ q = 𝟙 X := by
    dsimp only [q, p, sfGraphFirstPresentation, locallyClosedGraphS₁]
    exact pullback.lift_snd _ _ _
  let sq : IsPullback q ((sfGraphFirstPresentation c t).e) c.i p := by
    simpa only [q, p, sfGraphFirstPresentation] using
      (IsPullback.of_hasPullback p c.i).flip
  let N := (upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K
  let W := (upperStar (ModuleCat.{u + 1} A) c.i).leftDerivedFunctor.obj N
  let V := (upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj W
  let T := (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj N
  let v := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c
    t).a) q hs).hom.app W
  let α := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p c.g ((sfGraphFirstPresentation c t).p)
    pullback.condition).hom.app K
  let γ := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).hom.app N
  let η := (rightDerivedLowerStarIdIso A X).symm ≪≫
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).a) q (𝟙 X)
      hs).symm
  let ex := openImmersionLowerShriekLowerStarExchangeIso A sq
  let β := rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) p c.g ((sfGraphFirstPresentation c
    t).p) pullback.condition.symm
  have hη : ∀ M, ((derivedTensor (ModuleCat.{u + 1} A) X).flip.obj W).map (η.hom.app M) ≫
      (properStrength (ModuleCat.{u + 1} A) q W).app ((lowerStar (ModuleCat.{u + 1} A)
        ((sfGraphFirstPresentation c t).a)).rightDerivedFunctor.obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor.map
        ((properTwistedStrength (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).a) V v).app M)
          =
      η.hom.app (((derivedTensor (ModuleCat.{u + 1} A) X).flip.obj W).obj M) := by
    intro M
    exact section_projection A ((sfGraphFirstPresentation c t).a) q hs W M
  have hex : ∀ M, ((derivedTensor (ModuleCat.{u + 1} A) c.Z).flip.obj N).map (ex.hom.app M) ≫
      (properStrength (ModuleCat.{u + 1} A) p N).app ((openImmersionLowerShriek (ModuleCat.{u + 1}
        A) ((sfGraphFirstPresentation c t).e)).mapDerivedCategory.obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map ((openStrength (ModuleCat.{u + 1}
        A) ((sfGraphFirstPresentation c t).e) T γ).app M) =
    (openStrength (ModuleCat.{u + 1} A) c.i N (𝟙 W)).app ((lowerStar (ModuleCat.{u + 1} A)
      q).rightDerivedFunctor.obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map
        ((properStrength (ModuleCat.{u + 1} A) q W).app M) ≫
      ex.hom.app (((derivedTensor (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).U)).flip.obj
        V).obj M) := by
    intro M
    simpa only [T, γ, N, W, V, ex,
      openImmersionLowerShriekLowerStarExchangeIso, asIso_hom, openStrength_app,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id] using
      (mixed_twisted_projection (ModuleCat.{u + 1} A) sq N W (𝟙 W) M).symm
  have hβ := properStrength_compOfEq A p c.g ((sfGraphFirstPresentation c t).p)
    pullback.condition.symm K
  let d := (upperStar (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c
    t).a)).leftDerivedFunctor.map
    ((upperStar (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).e)).leftDerivedFunctor.map α ≫
      γ) ≫ v
  have hd : d ≫ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) c.i c.g f c.comm).inv.app K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).a)
        ((sfGraphFirstPresentation c t).e)).inv.app
          ((upperStar (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c
            t).p)).leftDerivedFunctor.obj K) ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (((sfGraphFirstPresentation c t).a) ≫
          ((sfGraphFirstPresentation c t).e)) ((sfGraphFirstPresentation c t).p) f
          ((Category.assoc _ _ _).trans (sfGraphFirstPresentation c t).fac).symm).inv.app K := by
    simpa only [d, α, γ, v, N, W, Functor.map_comp, Category.assoc] using
      section_graph_coefficient A ((sfGraphFirstPresentation c t).a) q ((sfGraphFirstPresentation c
        t).e) p c.i c.g ((sfGraphFirstPresentation c t).p) f hs sq.toCommSq
        pullback.condition c.comm
        ((Category.assoc _ _ _).trans (sfGraphFirstPresentation c t).fac).symm K
  have hw := word_strength_transport A ((sfGraphFirstPresentation c t).a) ((sfGraphFirstPresentation
    c t).e) ((sfGraphFirstPresentation c t).p) M K T V W α γ v
  have hside (L : DerivedCategoryModule A X) :
      (sfGraphFirstSideIso c t A).hom.app L =
      (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map (η.hom.app
            L)) ≫
        (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
          (ex.hom.app ((lowerStar (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c
            t).a)).rightDerivedFunctor.obj L)) ≫
        β.hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c
          t).e)).mapDerivedCategory.obj
          ((lowerStar (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c
            t).a)).rightDerivedFunctor.obj L)) := by
    simpa only [η, ex, β,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] using
      first_side_hom A c t hs L
  have h := graph_tensor_paste
    (lowerStar (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).a)).rightDerivedFunctor
      (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c
      t).e)).mapDerivedCategory
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor (lowerStar (ModuleCat.{u + 1} A)
      c.g).rightDerivedFunctor
    (lowerStar (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).p)).rightDerivedFunctor
    ((derivedTensor (ModuleCat.{u + 1} A) X).flip.obj W)
    ((derivedTensor (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).U)).flip.obj V)
    ((derivedTensor (ModuleCat.{u + 1} A) c.Z).flip.obj N)
    ((derivedTensor (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).P)).flip.obj T)
    ((derivedTensor (ModuleCat.{u + 1} A) Y).flip.obj K)
    (properTwistedStrength (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).a) V v)
      (properStrength (ModuleCat.{u + 1} A) q W)
    (openStrength (ModuleCat.{u + 1} A) c.i N (𝟙 W)) (openStrength (ModuleCat.{u + 1} A)
      ((sfGraphFirstPresentation c t).e) T γ)
    (properStrength (ModuleCat.{u + 1} A) p N) (properStrength (ModuleCat.{u + 1} A) c.g K)
    (properTwistedStrength (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).p) K α) η ex β hη
      hex hβ
    (sfGraphFirstSideIso c t A).hom hside M
  erw [hw] at h
  have hopen :
      (openStrength (ModuleCat.{u + 1} A) c.i N (𝟙 W)).app M =
        (((derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} A) c.i).inv.app M).app N) := by
    erw [openStrength_app]
    erw [((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map_id W]
    erw [((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory).map_id
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj W)]
    erw [Category.comp_id]
  erw [hopen] at h
  have hraw : ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((sfGraphFirstSideIso c t A).hom.app M)).app K ≫ (word_projection_raw A
          (sfGraphFirstPresentation c t) M K) ≫
      ((sfGraphFirstPresentation c t).functor A).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map d) =
    (compact_projection_raw A c M K) ≫ (sfGraphFirstSideIso c t A).hom.app
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj W) := by
    simpa only [word_projection_raw, compact_projection_raw, d,
      properStrength_app, openStrength_app,
      CategoryTheory.Functor.map_id, Category.comp_id, Functor.flip_obj_map, Functor.flip_obj_obj,
      EtaleGraphPresentation.functor, Functor.comp_map, Category.assoc] using h
  have hn := (sfGraphFirstSideIso c t A).hom.naturality
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map ((leftDerivedUpperStarComp (ModuleCat.{u +
      1} A) c.i c.g f c.comm).inv.app K))
  have hfinal : ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((sfGraphFirstSideIso c t A).hom.app M)).app K ≫ (word_projection_raw A
          (sfGraphFirstPresentation c t) M K) ≫
      ((sfGraphFirstPresentation c t).functor A).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c t).a)
            ((sfGraphFirstPresentation c t).e)).inv.app
              ((upperStar (ModuleCat.{u + 1} A) ((sfGraphFirstPresentation c
                t).p)).leftDerivedFunctor.obj K) ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (((sfGraphFirstPresentation c t).a) ≫
              ((sfGraphFirstPresentation c t).e)) ((sfGraphFirstPresentation c t).p) f
              ((Category.assoc _ _ _).trans
                (sfGraphFirstPresentation c t).fac).symm).inv.app K)) =
    (compact_projection_raw A c M K) ≫ (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1}
      A) c).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map ((leftDerivedUpperStarComp
          (ModuleCat.{u + 1} A) c.i c.g f c.comm).inv.app K)) ≫
      (sfGraphFirstSideIso c t A).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) := by
    rw [← hd, Functor.map_comp, Functor.map_comp]
    have hp := congrArg
      (fun z ↦ z ≫ ((sfGraphFirstPresentation c t).functor A).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map ((leftDerivedUpperStarComp
          (ModuleCat.{u + 1} A) c.i c.g f c.comm).inv.app K))) hraw
    simp only [Category.assoc] at hp
    erw [← hn] at hp
    exact hp
  exact projection_square_assoc hfinal

end AlgebraicGeometry.Etale
