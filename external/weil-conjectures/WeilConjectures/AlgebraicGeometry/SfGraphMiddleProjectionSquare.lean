/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionStages
import all WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import WeilConjectures.AlgebraicGeometry.ProperOpenFactorProjection

/-! # Projection compatibility across the graph intersection

Source: `LowerShriekComposition.lean`, eC, and Stacks Tags 0B56, 0GL1 and 0F7B.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
-- Preserve sharing of the derived-category instances in local functor definitions.
set_option cleanup.letToHave false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Match the braidings used by the generic derived-tensor comparisons.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

private def compStrength
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {T : C ⥤ C} {U : D ⥤ D} {V : E ⥤ E}
    (s : F ⋙ U ⟶ T ⋙ F) (t : G ⋙ V ⟶ U ⋙ G) :
    (F ⋙ G) ⋙ V ⟶ T ⋙ (F ⋙ G) where
  app M := t.app (F.obj M) ≫ G.map (s.app M)
  naturality M N f := by
    have ht := t.naturality (F.map f)
    have hs := s.naturality f
    dsimp only [Functor.comp_map] at ht hs ⊢
    rw [← Category.assoc, ht, Category.assoc, ← G.map_comp, hs, G.map_comp]
    simp only [Category.assoc]

private theorem compStrength_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {T : C ⥤ C} {U : D ⥤ D} {V : E ⥤ E}
    (s : F ⋙ U ⟶ T ⋙ F) (t : G ⋙ V ⟶ U ⋙ G) (M : C) :
    (compStrength s t).app M = t.app (F.obj M) ≫ G.map (s.app M) := rfl

private def StrengthCompatible
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} {T : C ⥤ C} {U : D ⥤ D}
    (e : F ≅ G) (s : F ⋙ U ⟶ T ⋙ F) (t : G ⋙ U ⟶ T ⋙ G) : Prop :=
  ∀ M, U.map (e.hom.app M) ≫ t.app M = s.app M ≫ e.hom.app (T.obj M)

private theorem strength_symm
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} {T : C ⥤ C} {U : D ⥤ D}
    {e : F ≅ G} {s : F ⋙ U ⟶ T ⋙ F} {t : G ⋙ U ⟶ T ⋙ G}
    (he : StrengthCompatible e s t) : StrengthCompatible e.symm t s := by
  intro M
  change U.map (e.inv.app M) ≫ s.app M = t.app M ≫ e.inv.app (T.obj M)
  apply (cancel_mono (e.hom.app (T.obj M))).1
  simp only [Category.assoc, e.inv_hom_id_app]
  rw [← he M]
  simp only [← Category.assoc, ← U.map_comp, e.inv_hom_id_app, U.map_id,
    Category.id_comp]
  exact (Category.comp_id (t.app M)).symm

private theorem strength_trans
    {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D} {T : C ⥤ C} {U : D ⥤ D}
    {e : F ≅ G} {d : G ≅ H}
    {s : F ⋙ U ⟶ T ⋙ F} {t : G ⋙ U ⟶ T ⋙ G} {v : H ⋙ U ⟶ T ⋙ H}
    (he : StrengthCompatible e s t) (hd : StrengthCompatible d t v) :
    StrengthCompatible (e ≪≫ d) s v := by
  intro M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [hd M, reassoc_of% (he M)]

private theorem strength_whiskerRight
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} {H : D ⥤ E} {T : C ⥤ C} {U : D ⥤ D} {V : E ⥤ E}
    {e : F ≅ G} {s : F ⋙ U ⟶ T ⋙ F} {t : G ⋙ U ⟶ T ⋙ G}
    (v : H ⋙ V ⟶ U ⋙ H) (he : StrengthCompatible e s t) :
    StrengthCompatible (Functor.isoWhiskerRight e H)
      (compStrength s v) (compStrength t v) := by
  intro M
  dsimp only [compStrength, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  have hv := v.naturality (e.hom.app M)
  dsimp only [Functor.comp_map] at hv
  rw [← Category.assoc, hv, Category.assoc, ← H.map_comp, he M, H.map_comp]
  simp only [Category.assoc]

private theorem strength_whiskerLeft
    {C D E : Type*} [Category C] [Category D] [Category E]
    {H : C ⥤ D} {F G : D ⥤ E} {T : C ⥤ C} {U : D ⥤ D} {V : E ⥤ E}
    {e : F ≅ G} {s : F ⋙ V ⟶ U ⋙ F} {t : G ⋙ V ⟶ U ⋙ G}
    (v : H ⋙ U ⟶ T ⋙ H) (he : StrengthCompatible e s t) :
    StrengthCompatible (Functor.isoWhiskerLeft H e)
      (compStrength v s) (compStrength v t) := by
  intro M
  dsimp only [compStrength, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  have hn := e.hom.naturality (v.app M)
  dsimp only [Functor.comp_obj] at hn
  rw [← Category.assoc, he (H.obj M), Category.assoc, ← hn]
  simp only [Category.assoc]

private theorem factor_twist_paste
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (J : D ⥤ E) (H : C ⥤ E)
    {W Z : E} {C₀ C₁ C₂ C₃ : C} {D₀ D₁ : D}
    {x : W ⟶ Z} {p : Z ⟶ H.obj C₀} {y : W ⟶ J.obj D₀}
    {a : C₀ ⟶ C₁} {c : C₁ ⟶ C₂} {d : C₂ ⟶ C₃}
    {q : D₀ ⟶ R.obj C₁} {v : D₀ ⟶ D₁} {q' : D₁ ⟶ R.obj C₂}
    {e : J.obj (R.obj C₁) ⟶ H.obj C₁} {e' : J.obj (R.obj C₃) ⟶ H.obj C₃}
    (h₀ : x ≫ p ≫ H.map a = y ≫ J.map q ≫ e)
    (hn : e ≫ H.map (c ≫ d) = J.map (R.map (c ≫ d)) ≫ e')
    (hp : v ≫ q' = q ≫ R.map c) :
    x ≫ p ≫ H.map (a ≫ c ≫ d) =
      y ≫ J.map v ≫ J.map (q' ≫ R.map d) ≫ e' := by
  calc
    _ = (x ≫ p ≫ H.map a) ≫ H.map (c ≫ d) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (y ≫ J.map q ≫ e) ≫ H.map (c ≫ d) := by rw [h₀]
    _ = y ≫ J.map q ≫ J.map (R.map (c ≫ d)) ≫ e' := by
      simp only [Category.assoc]
      rw [hn]
    _ = y ≫ J.map (q ≫ R.map c) ≫ J.map (R.map d) ≫ e' := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [← hp]
      simp only [Functor.map_comp, Category.assoc]

private theorem associator_whisker_component
    {C D₁ D₂ E F : Type*} [Category C] [Category D₁] [Category D₂]
    [Category E] [Category F]
    (R₁ : C ⥤ D₁) (J₁ : D₁ ⥤ E) (R₂ : C ⥤ D₂) (J₂ : D₂ ⥤ E)
    (H : E ⥤ F) (e : R₁ ⋙ J₁ ≅ R₂ ⋙ J₂) (M : C) :
    ((Functor.associator R₁ J₁ H).symm ≪≫ Functor.isoWhiskerRight e H ≪≫
      Functor.associator R₂ J₂ H).hom.app M = H.map (e.hom.app M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local implicit_reducible] EtaleGraphPresentation.functor
  sfGraphFirstPresentation sfGraphSecondPresentation

attribute [local irreducible] derivedTensor Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar lowerStar
  openImmersionLowerShriek rightDerivedLowerStarProjectionMap
  derivedOpenImmersionLowerShriekProjectionIso leftDerivedUpperStarComp
  properStrength properTwistedStrength openStrength
  rightDerivedLowerStarCompOpenImmersionLowerShriekIso

private theorem factorStrength_generic
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X V U : Scheme.{u}} (s : X ⟶ V) (j : V ⟶ U) (h : X ⟶ U)
    [IsOpenImmersion j] [IsProper h] (fac : s ≫ j = h)
    (N : DerivedCategory (Sheaf U.smallEtaleTopology B))
    (P : DerivedCategory (Sheaf V.smallEtaleTopology B))
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (vj : (upperStar (B) j).leftDerivedFunctor.obj N ⟶ P)
    (vs : (upperStar (B) s).leftDerivedFunctor.obj P ⟶ Q)
    (vh : (upperStar (B) h).leftDerivedFunctor.obj N ⟶ Q)
    (E : (lowerStar B s).rightDerivedFunctor ⋙
      (openImmersionLowerShriek B j).mapDerivedCategory ≅
      (lowerStar B h).rightDerivedFunctor)
    (h0 : ∀ M : DerivedCategory (Sheaf X.smallEtaleTopology B),
      ((derivedTensor B U).map (E.hom.app M)).app N ≫
        ((rightDerivedLowerStarProjectionMap B h).app M).app N ≫
        (lowerStar B h).rightDerivedFunctor.map
          (((derivedTensor B X).obj M).map
            ((leftDerivedUpperStarComp B s j h fac.symm).hom.app N)) =
      ((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app
        ((lowerStar B s).rightDerivedFunctor.obj M)).app N ≫
        (openImmersionLowerShriek B j).mapDerivedCategory.map
          (((rightDerivedLowerStarProjectionMap B s).app M).app
            ((upperStar B j).leftDerivedFunctor.obj N)) ≫
        E.hom.app (((derivedTensor B X).obj M).obj
          ((upperStar B s).leftDerivedFunctor.obj
            ((upperStar B j).leftDerivedFunctor.obj N))))
    (hc : (leftDerivedUpperStarComp (B) s j h fac.symm).hom.app N ≫
      (upperStar (B) s).leftDerivedFunctor.map vj ≫ vs = vh) :
    StrengthCompatible
      (T := (derivedTensor (B) X).flip.obj Q)
      (U := (derivedTensor (B) U).flip.obj N)
      E
      (compStrength (properTwistedStrength (B) s P vs)
        (openStrength (B) j N vj))
      (properTwistedStrength (B) h N vh) := by
  intro M
  let R := (lowerStar B s).rightDerivedFunctor
  let J := (openImmersionLowerShriek B j).mapDerivedCategory
  let H := (lowerStar B h).rightDerivedFunctor
  let T := (derivedTensor B X).obj M
  let a := (leftDerivedUpperStarComp B s j h fac.symm).hom.app N
  let b := (upperStar B s).leftDerivedFunctor.map vj ≫ vs
  have he := E.hom.naturality (T.map b)
  dsimp only [Functor.comp_map, Functor.comp_obj] at he
  have hp := properProjection_naturality_right B s M _ _ vj
  have h0 := h0 M
  have hn : E.hom.app (T.obj
      ((upperStar B s).leftDerivedFunctor.obj
        ((upperStar B j).leftDerivedFunctor.obj N))) ≫
      H.map (T.map ((upperStar B s).leftDerivedFunctor.map vj) ≫ T.map vs) =
      J.map (R.map (T.map ((upperStar B s).leftDerivedFunctor.map vj) ≫ T.map vs)) ≫
        E.hom.app (T.obj Q) := by
    simpa only [b, Functor.map_comp] using he.symm
  have hh := factor_twist_paste R J H
    (x := ((derivedTensor B U).map (E.hom.app M)).app N)
    (p := ((rightDerivedLowerStarProjectionMap B h).app M).app N)
    (y := ((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app (R.obj M)).app N)
    (a := T.map a) (c := T.map ((upperStar B s).leftDerivedFunctor.map vj))
    (d := T.map vs)
    (q := ((rightDerivedLowerStarProjectionMap B s).app M).app
      ((upperStar B j).leftDerivedFunctor.obj N))
    (v := ((derivedTensor B V).obj (R.obj M)).map vj)
    (q' := ((rightDerivedLowerStarProjectionMap B s).app M).app P)
    (e := E.hom.app (T.obj ((upperStar B s).leftDerivedFunctor.obj
      ((upperStar B j).leftDerivedFunctor.obj N))))
    (e' := E.hom.app (T.obj Q)) h0 hn hp
  have hv := congrArg T.map hc
  simp only [Functor.map_comp] at hv
  rw [hv] at hh
  simpa only [compStrength_app, properTwistedStrength_app, openStrength_app,
    Functor.flip_obj_obj, Functor.flip_obj_map, Functor.map_comp, Category.assoc] using hh

private theorem factorStrength
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V U : Scheme.{u}} (s : X ⟶ V) (j : V ⟶ U) (h : X ⟶ U)
    [IsOpenImmersion j] [IsProper h] (fac : s ≫ j = h)
    (N : DerivedCategoryModule A U) (P : DerivedCategoryModule A V)
    (Q : DerivedCategoryModule A X)
    (vj : (upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj N ⟶ P)
    (vs : (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.obj P ⟶ Q)
    (vh : (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj N ⟶ Q)
    (hc : (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s j h fac.symm).hom.app N ≫
      (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.map vj ≫ vs = vh) :
    StrengthCompatible
      (T := (derivedTensor (ModuleCat.{u + 1} A) X).flip.obj Q)
      (U := (derivedTensor (ModuleCat.{u + 1} A) U).flip.obj N)
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s j h fac)
      (compStrength (properTwistedStrength (ModuleCat.{u + 1} A) s P vs)
        (openStrength (ModuleCat.{u + 1} A) j N vj))
      (properTwistedStrength (ModuleCat.{u + 1} A) h N vh) := by
  exact factorStrength_generic (ModuleCat.{u + 1} A) s j h fac N P Q vj vs vh
    (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s j h fac)
    (fun M ↦ properOpenFactor_projection A s j h fac M N) hc

private theorem strength_assoc
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {R : C ⥤ D} {S : D ⥤ E} {H : E ⥤ F}
    {T : C ⥤ C} {U : D ⥤ D} {V : E ⥤ E} {W : F ⥤ F}
    (r : R ⋙ U ⟶ T ⋙ R) (s : S ⋙ V ⟶ U ⋙ S) (h : H ⋙ W ⟶ V ⋙ H) :
    StrengthCompatible (Functor.associator R S H)
      (compStrength (compStrength r s) h) (compStrength r (compStrength s h)) := by
  intro M
  simp only [Functor.associator_hom_app, compStrength, Functor.map_comp,
    Functor.comp_obj, Functor.comp_map, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Category.assoc]
  exact (Category.comp_id _).symm

private noncomputable def innerStrength
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X V U : Scheme.{u}} (s : X ⟶ V) (b : V ⟶ U) (a : X ⟶ U)
    [IsOpenImmersion b] (fac : s ≫ b = a)
    (N : DerivedCategory (Sheaf U.smallEtaleTopology B))
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (v : (upperStar (B) a).leftDerivedFunctor.obj N ⟶ Q) :=
  compStrength
    (properTwistedStrength (B) s
      ((upperStar (B) b).leftDerivedFunctor.obj N)
      ((leftDerivedUpperStarComp (B) s b a fac.symm).inv.app N ≫ v))
    (openStrength (B) b N (𝟙 _))

private theorem factor_coefficient
    (A : Type (u + 1)) [CommRing A]
    {X V W U : Scheme.{u}} (s : X ⟶ V) (j : V ⟶ W) (b : W ⟶ U)
    (h : X ⟶ W) (k : V ⟶ U) (a : X ⟶ U)
    (hs : s ≫ j = h) (hj : j ≫ b = k) (ha : h ≫ b = a)
    (N : DerivedCategoryModule A U) (Q : DerivedCategoryModule A X)
    (v : (upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.obj N ⟶ Q) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s j h hs.symm).hom.app
        ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj N) ≫
      (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j b k hj.symm).inv.app N) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s k a
        (by rw [← ha, ← hs, Category.assoc, hj])).inv.app N ≫ v =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h b a ha.symm).inv.app N ≫ v := by
  have hc := leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} A) s j b h k a hs.symm hj.symm ha.symm N
  rw [reassoc_of% hc]
  simp only [Iso.hom_inv_id_app_assoc]

private noncomputable def intersectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X O₁ O₂ T : Scheme.{u}} (b₁ : O₁ ⟶ T) (b₂ : O₂ ⟶ T)
    [IsOpenImmersion b₁] [IsOpenImmersion b₂]
    (s₁ : X ⟶ O₁) (s₂ : X ⟶ O₂) [IsProper s₁] [IsProper s₂]
    (s : X ⟶ pullback b₁ b₂)
    (h₁ : s ≫ pullback.fst b₁ b₂ = s₁) (h₂ : s ≫ pullback.snd b₁ b₂ = s₂) :
    (lowerStar (ModuleCat.{u + 1} A) s₁).rightDerivedFunctor ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) b₁).mapDerivedCategory ≅
      (lowerStar (ModuleCat.{u + 1} A) s₂).rightDerivedFunctor ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) b₂).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s _ s₁ h₁).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) _ _).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
          pullback.condition ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s _ s₂ h₂) _

private theorem open_congr_refl
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
      (rfl : j = j) = Iso.refl _ := rfl

private theorem open_congr_symm
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {j k : X ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) :
    (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h).symm =
      mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h.symm := by
  cases h
  rfl

private theorem intersection_strength
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X O₁ O₂ T : Scheme.{u}} (b₁ : O₁ ⟶ T) (b₂ : O₂ ⟶ T)
    [IsOpenImmersion b₁] [IsOpenImmersion b₂]
    (s₁ : X ⟶ O₁) (s₂ : X ⟶ O₂) [IsProper s₁] [IsProper s₂]
    (s : X ⟶ pullback b₁ b₂)
    (h₁ : s ≫ pullback.fst b₁ b₂ = s₁) (h₂ : s ≫ pullback.snd b₁ b₂ = s₂)
    (a : X ⟶ T) (ha₁ : s₁ ≫ b₁ = a) (ha₂ : s₂ ≫ b₂ = a)
    (N : DerivedCategoryModule A T) (Q : DerivedCategoryModule A X)
    (v : (upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.obj N ⟶ Q) :
    StrengthCompatible (intersectionIso A b₁ b₂ s₁ s₂ s h₁ h₂)
      (innerStrength (ModuleCat.{u + 1} A) s₁ b₁ a ha₁ N Q v)
      (innerStrength (ModuleCat.{u + 1} A) s₂ b₂ a ha₂ N Q v) := by
  let B := ModuleCat.{u + 1} A
  let u₁ := pullback.fst b₁ b₂
  let u₂ := pullback.snd b₁ b₂
  let b := u₁ ≫ b₁
  have hb : u₂ ≫ b₂ = b := pullback.condition.symm
  have hs : s ≫ b = a := by rw [← Category.assoc, h₁, ha₁]
  let N₁ := (upperStar B b₁).leftDerivedFunctor.obj N
  let N₂ := (upperStar B b₂).leftDerivedFunctor.obj N
  let N₁₂ := (upperStar B b).leftDerivedFunctor.obj N
  let w₁ := (leftDerivedUpperStarComp B u₁ b₁ b rfl).inv.app N
  let w₂ := (leftDerivedUpperStarComp B u₂ b₂ b hb.symm).inv.app N
  let r := properTwistedStrength B s N₁₂
    ((leftDerivedUpperStarComp B s b a hs.symm).inv.app N ≫ v)
  let t₁ := openStrength B u₁ N₁ w₁
  let t₂ := openStrength B u₂ N₂ w₂
  let j₁ := openStrength B b₁ N (𝟙 _)
  let j₂ := openStrength B b₂ N (𝟙 _)
  let j := openStrength B b N (𝟙 _)
  let r₁ := properTwistedStrength B s₁ N₁
    ((leftDerivedUpperStarComp B s₁ b₁ a ha₁.symm).inv.app N ≫ v)
  let r₂ := properTwistedStrength B s₂ N₂
    ((leftDerivedUpperStarComp B s₂ b₂ a ha₂.symm).inv.app N ≫ v)
  let E₁ := rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s u₁ s₁ h₁
  let E₂ := rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s u₂ s₂ h₂
  have he₁ : StrengthCompatible E₁ (compStrength r t₁) r₁ := by
    apply factorStrength A s u₁ s₁ h₁ N₁ N₁₂ Q w₁ _ _
    exact factor_coefficient A s u₁ b₁ s₁ b a h₁ rfl ha₁ N Q v
  have he₂ : StrengthCompatible E₂ (compStrength r t₂) r₂ := by
    apply factorStrength A s u₂ s₂ h₂ N₂ N₁₂ Q w₂ _ _
    exact factor_coefficient A s u₂ b₂ s₂ b a h₂ hb ha₂ N Q v
  let O₁ := (mapDerivedCategoryOpenImmersionLowerShriekComp B u₁ b₁).symm
  let O₂ := (mapDerivedCategoryOpenImmersionLowerShriekComp B u₂ b₂).symm ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekCongr B hb
  have ho₁ : StrengthCompatible O₁ (compStrength t₁ j₁) j := by
    intro M
    have hh := openStrength_comp B u₁ b₁ b rfl N N₁ N₁₂ (𝟙 _) w₁ M
    erw [open_congr_refl A b] at hh
    erw [Iso.trans_refl] at hh
    simpa only [compStrength_app, w₁, w₂, Functor.comp_obj, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id, Iso.hom_inv_id_app, Category.assoc,
      Iso.trans_refl] using hh
  have ho₂ : StrengthCompatible O₂ (compStrength t₂ j₂) j := by
    intro M
    have hh := openStrength_comp B u₂ b₂ b hb N N₂ N₁₂ (𝟙 _) w₂ M
    simpa only [compStrength_app, w₁, w₂, Functor.comp_obj, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id, Iso.hom_inv_id_app, Category.assoc,
      Iso.trans_refl] using hh
  have hh := strength_trans
    (strength_trans
      (strength_trans
        (strength_trans
          (strength_whiskerRight j₁ (strength_symm he₁)) (strength_assoc r t₁ j₁))
        (strength_whiskerLeft r (strength_trans ho₁ (strength_symm ho₂))))
      (strength_symm (strength_assoc r t₂ j₂)))
    (strength_whiskerRight j₂ he₂)
  convert hh using 1
  · simp only [intersectionIso, E₁, E₂, O₁, O₂, Iso.trans_symm, Iso.symm_symm_eq,
      Functor.isoWhiskerLeft_trans, Iso.trans_assoc]
    erw [open_congr_symm A hb]
  · rfl
  · rfl

private noncomputable def projectionWord
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X V P Y : Scheme.{u}} {f : X ⟶ Y}
    (s : X ⟶ V) (b : V ⟶ P) (p : P ⟶ Y) [IsOpenImmersion b]
    (facf : s ≫ b ≫ p = f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((derivedTensor B Y).obj
      (((lowerStar B s).rightDerivedFunctor ⋙
        (openImmersionLowerShriek B b).mapDerivedCategory ⋙
        (lowerStar B p).rightDerivedFunctor).obj M)).obj K ⟶
      ((lowerStar B s).rightDerivedFunctor ⋙
        (openImmersionLowerShriek B b).mapDerivedCategory ⋙
        (lowerStar B p).rightDerivedFunctor).obj
          (((derivedTensor B X).obj M).obj
            ((upperStar B f).leftDerivedFunctor.obj K)) := by
  let R := (lowerStar B p).rightDerivedFunctor
  let J := (openImmersionLowerShriek B b).mapDerivedCategory
  let S := (lowerStar B s).rightDerivedFunctor
  let Lp := (upperStar B p).leftDerivedFunctor
  let Le := (upperStar B b).leftDerivedFunctor
  let La := (upperStar B s).leftDerivedFunctor
  let c : (Lp ⋙ Le) ⋙ La ≅ (upperStar B f).leftDerivedFunctor :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp B s b).symm ≪≫
      (leftDerivedUpperStarComp B (s ≫ b) p f
        ((Category.assoc s b p).trans facf).symm).symm
  exact ((rightDerivedLowerStarProjectionMap B p).app (J.obj (S.obj M))).app K ≫
    R.map (((derivedOpenImmersionLowerShriekProjectionIso B b).inv.app
      (S.obj M)).app (Lp.obj K)) ≫
    R.map (J.map (((rightDerivedLowerStarProjectionMap B s).app M).app
      (Le.obj (Lp.obj K)))) ≫
    R.map (J.map (S.map (((derivedTensor B X).obj M).map (c.hom.app K))))

private theorem word_strength_generic
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X V P Y : Scheme.{u}} {f : X ⟶ Y}
    (s : X ⟶ V) (b : V ⟶ P) (p : P ⟶ Y) [IsOpenImmersion b]
    (facf : s ≫ b ≫ p = f)
    (a : X ⟶ P) (fac : s ≫ b = a)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (properStrength B p K).app
        ((openImmersionLowerShriek B b).mapDerivedCategory.obj
          ((lowerStar B s).rightDerivedFunctor.obj M)) ≫
      (lowerStar B p).rightDerivedFunctor.map
        ((innerStrength B s b a fac
          ((upperStar B p).leftDerivedFunctor.obj K)
          ((upperStar B f).leftDerivedFunctor.obj K)
          ((leftDerivedUpperStarComp B a p f
            (by rw [← fac, Category.assoc, facf])).inv.app K)).app M) =
      projectionWord B s b p facf M K := by
  subst a
  simp only [innerStrength, compStrength_app, properStrength_app, properTwistedStrength_app,
    openStrength_app, CategoryTheory.Functor.map_id, Functor.map_comp,
    Category.assoc, projectionWord, Iso.trans_hom, Iso.symm_hom,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.comp_obj, Category.id_comp]
  erw [(openImmersionLowerShriek B b).mapDerivedCategory.map_id,
    (lowerStar B p).rightDerivedFunctor.map_id, Category.id_comp]

-- Branch usage depends on the imported wrapper version, not on the mathematical goal.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem word_strength_source
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f)
    (a : X ⟶ t.P) (fac : t.a ≫ t.e = a)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (properStrength (ModuleCat.{u + 1} A) t.p K).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) t.e).mapDerivedCategory.obj
          ((lowerStar (ModuleCat.{u + 1} A) t.a).rightDerivedFunctor.obj M)) ≫
      (lowerStar (ModuleCat.{u + 1} A) t.p).rightDerivedFunctor.map
        ((innerStrength (ModuleCat.{u + 1} A) t.a t.e a fac
          ((upperStar (ModuleCat.{u + 1} A) t.p).leftDerivedFunctor.obj K)
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a t.p f
            (by rw [← fac, Category.assoc, t.fac])).inv.app K)).app M) =
      sfGraphWordProjection A t M K := by
  subst a
  -- Support the published inline body and the current generic graph-word wrapper.
  first
  | simp only [innerStrength, compStrength_app, properStrength_app, properTwistedStrength_app,
      openStrength_app, CategoryTheory.Functor.map_id, Functor.map_comp,
      Category.assoc, sfGraphWordProjection, sfGraphProjectionWord, Functor.comp_obj]
    erw [(openImmersionLowerShriek (ModuleCat.{u + 1} A) t.e).mapDerivedCategory.map_id,
      (lowerStar (ModuleCat.{u + 1} A) t.p).rightDerivedFunctor.map_id, Category.id_comp]
  | simp only [innerStrength, compStrength_app, properStrength_app, properTwistedStrength_app,
      openStrength_app, CategoryTheory.Functor.map_id, Functor.map_comp,
      Category.assoc, sfGraphWordProjection, Iso.trans_hom, Iso.symm_hom,
      Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      NatTrans.comp_app, Functor.comp_obj, Category.id_comp]
    erw [(openImmersionLowerShriek (ModuleCat.{u + 1} A) t.e).mapDerivedCategory.map_id,
      (lowerStar (ModuleCat.{u + 1} A) t.p).rightDerivedFunctor.map_id, Category.id_comp]

private theorem projectionWord_eq_source
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    projectionWord (ModuleCat.{u + 1} A) t.a t.e t.p t.fac M K =
      sfGraphWordProjection A t M K := by
  exact (word_strength_generic (ModuleCat.{u + 1} A) t.a t.e t.p t.fac
    (t.a ≫ t.e) rfl M K).symm.trans
      (word_strength_source A t (t.a ≫ t.e) rfl M K)

private theorem outer_projection_paste
    {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) (T : C ⥤ C) (U : D ⥤ D)
    (p : R ⋙ U ⟶ T ⋙ R)
    {P₁ P₂ Q₁ Q₂ : C} {e : P₁ ⟶ P₂} {e' : Q₁ ⟶ Q₂}
    {r₁ : T.obj P₁ ⟶ Q₁} {r₂ : T.obj P₂ ⟶ Q₂}
    (h : T.map e ≫ r₂ = r₁ ≫ e') :
    U.map (R.map e) ≫ p.app P₂ ≫ R.map r₂ =
      p.app P₁ ≫ R.map r₁ ≫ R.map e' := by
  have hn := p.naturality e
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← R.map_comp, h, R.map_comp]

private theorem outer_projection_paste_eq
    {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) (T : C ⥤ C) (U : D ⥤ D)
    (p : R ⋙ U ⟶ T ⋙ R)
    {P₁ P₂ Q₁ Q₂ : C} {e : P₁ ⟶ P₂} {e' : Q₁ ⟶ Q₂}
    {r₁ : T.obj P₁ ⟶ Q₁} {r₂ : T.obj P₂ ⟶ Q₂}
    {φ : R.obj P₁ ⟶ R.obj P₂} {ψ : R.obj Q₁ ⟶ R.obj Q₂}
    {w₁ : U.obj (R.obj P₁) ⟶ R.obj Q₁}
    {w₂ : U.obj (R.obj P₂) ⟶ R.obj Q₂}
    (h : T.map e ≫ r₂ = r₁ ≫ e')
    (hw₁ : p.app P₁ ≫ R.map r₁ = w₁)
    (hw₂ : p.app P₂ ≫ R.map r₂ = w₂)
    (hφ : φ = R.map e) (hψ : ψ = R.map e') :
    U.map φ ≫ w₂ = w₁ ≫ ψ := by
  rw [hφ, hψ, ← hw₁, ← hw₂]
  simpa only [Category.assoc] using outer_projection_paste R T U p h

private theorem outer_projection_paste_etale
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {P Y : Scheme.{u}} (p : P ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    {P₁ P₂ Q₁ Q₂ : DerivedCategory (Sheaf P.smallEtaleTopology B)}
    {e : P₁ ⟶ P₂} {e' : Q₁ ⟶ Q₂}
    {r₁ : (((derivedTensor B P).obj P₁).obj
      ((upperStar B p).leftDerivedFunctor.obj K)) ⟶ Q₁}
    {r₂ : (((derivedTensor B P).obj P₂).obj
      ((upperStar B p).leftDerivedFunctor.obj K)) ⟶ Q₂}
    {φ : (lowerStar B p).rightDerivedFunctor.obj P₁ ⟶
      (lowerStar B p).rightDerivedFunctor.obj P₂}
    {ψ : (lowerStar B p).rightDerivedFunctor.obj Q₁ ⟶
      (lowerStar B p).rightDerivedFunctor.obj Q₂}
    {w₁ : ((derivedTensor B Y).obj
      ((lowerStar B p).rightDerivedFunctor.obj P₁)).obj K ⟶
      (lowerStar B p).rightDerivedFunctor.obj Q₁}
    {w₂ : ((derivedTensor B Y).obj
      ((lowerStar B p).rightDerivedFunctor.obj P₂)).obj K ⟶
      (lowerStar B p).rightDerivedFunctor.obj Q₂}
    (h : ((derivedTensor B P).flip.obj
      ((upperStar B p).leftDerivedFunctor.obj K)).map e ≫ r₂ = r₁ ≫ e')
    (hw₁ : (properStrength B p K).app P₁ ≫
      (lowerStar B p).rightDerivedFunctor.map r₁ = w₁)
    (hw₂ : (properStrength B p K).app P₂ ≫
      (lowerStar B p).rightDerivedFunctor.map r₂ = w₂)
    (hφ : φ = (lowerStar B p).rightDerivedFunctor.map e)
    (hψ : ψ = (lowerStar B p).rightDerivedFunctor.map e') :
    ((derivedTensor B Y).map φ).app K ≫ w₂ = w₁ ≫ ψ := by
  exact outer_projection_paste_eq (lowerStar B p).rightDerivedFunctor
    ((derivedTensor B P).flip.obj ((upperStar B p).leftDerivedFunctor.obj K))
    ((derivedTensor B Y).flip.obj K) (properStrength B p K)
    h hw₁ hw₂ hφ hψ

-- Construct these terms before specializing the coefficient category. This keeps the
-- HasSmallSiteSheafify certificates inside the generic definitions.
private noncomputable def graphSquarePullbackObj
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    DerivedCategory (Sheaf X.smallEtaleTopology B) :=
  (upperStar B f).leftDerivedFunctor.obj K

private noncomputable def graphSquarePullbackCompInv
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X P Y : Scheme.{u}} (a : X ⟶ P) (p : P ⟶ Y) (f : X ⟶ Y)
    (haf : f = a ≫ p) (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    graphSquarePullbackObj B a (graphSquarePullbackObj B p K) ⟶ graphSquarePullbackObj B f K :=
  (leftDerivedUpperStarComp B a p f haf).inv.app K

private theorem word_middle_projection_generic
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)]
    [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X O₁ O₂ P Y : Scheme.{u}} {f : X ⟶ Y}
    (s₁ : X ⟶ O₁) (b₁ : O₁ ⟶ P) (s₂ : X ⟶ O₂) (b₂ : O₂ ⟶ P)
    [IsOpenImmersion b₁] [IsOpenImmersion b₂] (p : P ⟶ Y)
    (hfac₁ : s₁ ≫ b₁ ≫ p = f) (hfac₂ : s₂ ≫ b₂ ≫ p = f)
    (a : X ⟶ P) (ha₁ : s₁ ≫ b₁ = a) (ha₂ : s₂ ≫ b₂ = a) (haf : f = a ≫ p)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (e : (lowerStar B s₁).rightDerivedFunctor ⋙
        (openImmersionLowerShriek B b₁).mapDerivedCategory ≅
      (lowerStar B s₂).rightDerivedFunctor ⋙
        (openImmersionLowerShriek B b₂).mapDerivedCategory)
    (h : StrengthCompatible e
      (innerStrength B s₁ b₁ a ha₁ (graphSquarePullbackObj B p K) (graphSquarePullbackObj B f K)
        (graphSquarePullbackCompInv B a p f haf K))
      (innerStrength B s₂ b₂ a ha₂ (graphSquarePullbackObj B p K) (graphSquarePullbackObj B f K)
        (graphSquarePullbackCompInv B a p f haf K)))
    (E : ((lowerStar B s₁).rightDerivedFunctor ⋙
        (openImmersionLowerShriek B b₁).mapDerivedCategory ⋙
        (lowerStar B p).rightDerivedFunctor) ≅
      ((lowerStar B s₂).rightDerivedFunctor ⋙
        (openImmersionLowerShriek B b₂).mapDerivedCategory ⋙
        (lowerStar B p).rightDerivedFunctor))
    (hE : ∀ Z, E.hom.app Z = (lowerStar B p).rightDerivedFunctor.map (e.hom.app Z))
    {w₁ : ((derivedTensor B Y).obj (((lowerStar B s₁).rightDerivedFunctor ⋙
        (openImmersionLowerShriek B b₁).mapDerivedCategory ⋙
        (lowerStar B p).rightDerivedFunctor).obj M)).obj K ⟶
      (((lowerStar B s₁).rightDerivedFunctor ⋙
        (openImmersionLowerShriek B b₁).mapDerivedCategory ⋙
        (lowerStar B p).rightDerivedFunctor).obj
        (((derivedTensor B X).obj M).obj (graphSquarePullbackObj B f K)))}
    {w₂ : ((derivedTensor B Y).obj (((lowerStar B s₂).rightDerivedFunctor ⋙
        (openImmersionLowerShriek B b₂).mapDerivedCategory ⋙
        (lowerStar B p).rightDerivedFunctor).obj M)).obj K ⟶
      (((lowerStar B s₂).rightDerivedFunctor ⋙
        (openImmersionLowerShriek B b₂).mapDerivedCategory ⋙
        (lowerStar B p).rightDerivedFunctor).obj
        (((derivedTensor B X).obj M).obj (graphSquarePullbackObj B f K)))}
    (hw₁ : projectionWord B s₁ b₁ p hfac₁ M K = w₁)
    (hw₂ : projectionWord B s₂ b₂ p hfac₂ M K = w₂) :
    ((derivedTensor B Y).map (E.hom.app M)).app K ≫ w₂ =
      w₁ ≫ E.hom.app (((derivedTensor B X).obj M).obj (graphSquarePullbackObj B f K)) := by
  have h₁ := (word_strength_generic B s₁ b₁ p hfac₁ a ha₁ M K).trans hw₁
  have h₂ := (word_strength_generic B s₂ b₂ p hfac₂ a ha₂ M K).trans hw₂
  exact outer_projection_paste_etale B p K (h M) h₁ h₂ (hE M) (hE _)

/-- Projection compatibility across the graph intersection.

Source: `LowerShriekComposition.lean`, eC; the tensor calculation uses Stacks
Tags 0B56, 0GL1 and 0F7B (auxiliary; not a blueprint node).

Proof in words. Let O12 be the intersection of the two supporting opens b1:O1 -> T and
b2:O2 -> T, with projections u1,u2 and proper graph s12. Since u1 and u2 are
monomorphisms and s12 ui = si, the identity-top squares relating s12 to si
are Cartesian. Specialize the proper/open tensor square to each of these
squares. Remove extension by the identity using its canonical unitor; the
exchange is then precisely rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
with the normalization in its defining unit/counit formula. Solve the first
square for its inverse comparison by cancelling isomorphism components.
Whisker by Jb1 and Jb2 and use open projection composition for u1 b1 and u2 b2.
The equality u1 b1 = u2 b2 is pullback.condition, so the two open-composition
coefficient comparisons agree after the canonical congruence comparison. Paste
these squares to obtain compatibility of B12 with the successive inner proper
and open projections. Whisker by R(p1 p) and use naturality of its projection.
The canonical pullback composition identities identify the final coefficient
paths with those of the two sfGraphWordProjection maps. This proves the stated
square. Empty intersections and zero objects satisfy the same identities; no
projection is inverted.
-/
theorem sfGraphMiddleIso_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((sfGraphMiddleIso c t A).hom.app M)).app K ≫
      sfGraphWordProjection A (sfGraphSecondPresentation c t) M K =
    sfGraphWordProjection A (sfGraphFirstPresentation c t) M K ≫
      (sfGraphMiddleIso c t A).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) := by
  let B := ModuleCat.{u + 1} A
  let h := (Category.assoc t.a t.e t.p).trans (t.fac.trans c.comm)
  let P := pullback t.p c.g
  let O₁ := pullback (pullback.snd t.p c.g) c.i
  let O₂ := pullback (pullback.fst t.p c.g) t.e
  let b₁ : O₁ ⟶ P := pullback.fst (pullback.snd t.p c.g) c.i
  let b₂ : O₂ ⟶ P := pullback.fst (pullback.fst t.p c.g) t.e
  let s₁ : X ⟶ O₁ := locallyClosedGraphS₁ t.a t.e t.p c.i c.g h
  let s₂ : X ⟶ O₂ := locallyClosedGraphS₂ t.a t.e t.p c.i c.g h
  let s : X ⟶ pullback b₁ b₂ := locallyClosedGraphS₁₂ t.a t.e t.p c.i c.g h
  let a : X ⟶ P := locallyClosedGraphV t.a t.e t.p c.i c.g h
  let p : P ⟶ Y := pullback.fst t.p c.g ≫ t.p
  have hs₁ : s ≫ pullback.fst b₁ b₂ = s₁ := pullback.lift_fst _ _ _
  have hs₂ : s ≫ pullback.snd b₁ b₂ = s₂ := pullback.lift_snd _ _ _
  have ha₁ : s₁ ≫ b₁ = a := pullback.lift_fst _ _ _
  have ha₂ : s₂ ≫ b₂ = a := pullback.lift_fst _ _ _
  have haf : f = a ≫ p := by
    dsimp only [a, p, locallyClosedGraphV]
    rw [pullback.lift_fst_assoc]
    exact ((Category.assoc t.a t.e t.p).trans t.fac).symm
  have : IsProper s₁ := sfGraphFirst_proper c t
  have : IsProper s₂ := sfGraphSecond_proper c t
  let N := graphSquarePullbackObj B p K
  let Q := graphSquarePullbackObj B f K
  let v := graphSquarePullbackCompInv B a p f haf K
  have hi := intersection_strength A b₁ b₂ s₁ s₂ s hs₁ hs₂ a ha₁ ha₂ N Q v
  have hfac₁ : s₁ ≫ b₁ ≫ p = f := by
    rw [← Category.assoc, ha₁]
    exact haf.symm
  have hfac₂ : s₂ ≫ b₂ ≫ p = f := by
    rw [← Category.assoc, ha₂]
    exact haf.symm
  have hE (Z : DerivedCategoryModule A X) :
      (sfGraphMiddleIso c t A).hom.app Z =
        (lowerStar B p).rightDerivedFunctor.map
          ((intersectionIso A b₁ b₂ s₁ s₂ s hs₁ hs₂).hom.app Z) := by
    exact associator_whisker_component _ _ _ _ _
      (intersectionIso A b₁ b₂ s₁ s₂ s hs₁ hs₂) Z
  exact word_middle_projection_generic B s₁ b₁ s₂ b₂ p hfac₁ hfac₂ a ha₁ ha₂ haf M K
    (intersectionIso A b₁ b₂ s₁ s₂ s hs₁ hs₂) hi (sfGraphMiddleIso c t A) hE
    (projectionWord_eq_source A (sfGraphFirstPresentation c t) M K)
    (projectionWord_eq_source A (sfGraphSecondPresentation c t) M K)

end AlgebraicGeometry.Etale
