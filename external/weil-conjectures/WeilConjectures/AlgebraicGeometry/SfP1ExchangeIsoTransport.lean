/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1ChartExchange
import WeilConjectures.AlgebraicGeometry.ProperSelfExchangeForgetSupports
import WeilConjectures.AlgebraicGeometry.SfIsoPushPullUnitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar

/-! # Exchange pasting across an isomorphism over the base

This is the coefficient-independent exchange square, before any trace or unit map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
attribute [local irreducible] upperStar lowerStar rightDerivedLowerShriek
  rightDerivedLowerShriekIsoRightDerivedLowerStar instCategoryDerivedCategory
attribute [local semireducible] projection
attribute [local implicit_reducible] projection projectiveLineDiagonalProjection

private lemma square_hom
    (A : Type (u + 1)) [CommRing A]
    {W X Z Y : Scheme.{u}} {v : W ⟶ Z} {p : W ⟶ X}
    {f : Z ⟶ Y} {g : X ⟶ Y} (sq : CommSq v p f g)
    (d : W ⟶ Y) (h : d = v ≫ f) (K : DerivedCategoryModule A Y) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app K =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p g d (h.trans sq.w)).inv.app K ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v f d h).hom.app K := by
  subst d
  rfl

private lemma source_square
    (A : Type (u + 1)) [CommRing A]
    {W X Z Y E : Scheme.{u}} {v : W ⟶ Z} {p : W ⟶ X}
    {f : Z ⟶ Y} {g : X ⟶ Y} (sq : CommSq v p f g)
    (e : E ⟶ Z) (k : W ⟶ E) (r : E ⟶ Y)
    (hv : v = k ≫ e) (hr : r = e ≫ f) (sq' : CommSq k p r g)
    (K : DerivedCategoryModule A Y) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq').hom.app K ≫
      (ordinaryFinitePullback A k).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e f r hr).hom.app K) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) k e v hv).inv.app
        ((ordinaryFinitePullback A f).obj K) =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app K := by
  have h := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    k e f v r (v ≫ f) hv hr rfl K
  rw [square_hom A sq' (v ≫ f) (by rw [hv, hr, Category.assoc])]
  rw [square_hom A sq (v ≫ f) rfl]
  simp only [Category.assoc]
  dsimp only [ordinaryFinitePullback]
  rw [reassoc_of% h, Iso.hom_inv_id_app, Category.comp_id]

private lemma source_exchange
    (A : Type (u + 1)) [CommRing A]
    {W X Z Y E : Scheme.{u}} {v : W ⟶ Z} {p : W ⟶ X}
    {f : Z ⟶ Y} {g : X ⟶ Y} (sq : CommSq v p f g)
    (e : E ⟶ Z) (k : W ⟶ E) (r : E ⟶ Y)
    (hv : v = k ≫ e) (hr : r = e ≫ f) (sq' : CommSq k p r g)
    (M : DerivedCategoryModule A Z) :
    (ordinaryFinitePullback A g).map
        ((ordinaryFinitePushforward A f).map
            ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app M) ≫
          (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) e f r hr).app
            ((ordinaryFinitePullback A e).obj M)) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq').app
        ((ordinaryFinitePullback A e).obj M) ≫
      (ordinaryFinitePushforward A p).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) k e v hv).inv.app M) =
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app M := by
  let B := ModuleCat.{u + 1} A
  apply ((derivedUpperStarLowerStarAdjunction B p).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [Adjunction.counit_naturality,
    derivedUpperStar_map_derivedBaseChangeMap_app_counit_assoc]
  have ns := (derivedSquareUpperStarIso B sq').hom.naturality
    ((rightDerivedLowerStarCompHom B e f r hr).app
      ((ordinaryFinitePullback A e).obj M))
  dsimp only [B, ordinaryFinitePullback, ordinaryFinitePushforward,
    Functor.comp_map, Functor.comp_obj] at ns
  dsimp only [B, ordinaryFinitePullback, ordinaryFinitePushforward] at ⊢
  rw [reassoc_of% ns, ← Functor.map_comp_assoc,
    map_rightDerivedLowerStarCompHom_app_counit]
  simp only [Functor.map_comp, Category.assoc]
  have nu := (derivedSquareUpperStarIso B sq').hom.naturality
    ((ordinaryFinitePushforward A f).map
      ((derivedUpperStarLowerStarAdjunction B e).unit.app M))
  have nc := (leftDerivedUpperStarComp B e f r hr).hom.naturality
    ((ordinaryFinitePushforward A f).map
      ((derivedUpperStarLowerStarAdjunction B e).unit.app M))
  have ne := (derivedUpperStarLowerStarAdjunction B f).counit.naturality
    ((derivedUpperStarLowerStarAdjunction B e).unit.app M)
  dsimp only [B, ordinaryFinitePullback, ordinaryFinitePushforward,
    Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj] at nu nc ne ⊢
  rw [reassoc_of% nu, ← Functor.map_comp_assoc, nc, Functor.map_comp_assoc]
  rw [← (upperStar (ModuleCat.{u + 1} A) k).leftDerivedFunctor.map_comp_assoc
    ((upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor.map
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
          ((derivedUpperStarLowerStarAdjunction B e).unit.app M)))) _]
  rw [← (upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor.map_comp, ne]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (upperStar (ModuleCat.{u + 1} A) k).leftDerivedFunctor.map_comp_assoc
    ((upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor.map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app M)) _]
  erw [(derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).left_triangle_components M]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have nn := (leftDerivedUpperStarComp B k e v hv).inv.naturality
    ((derivedUpperStarLowerStarAdjunction B f).counit.app M)
  dsimp only [B, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at nn
  rw [nn, derivedUpperStar_map_derivedBaseChangeMap_app_counit]
  have hh := source_square A sq e k r hv hr sq'
    ((ordinaryFinitePushforward A f).obj M)
  dsimp only [ordinaryFinitePullback, ordinaryFinitePushforward] at hh
  simpa only [B, ordinaryFinitePullback, Functor.comp_obj, Functor.id_obj,
    Category.assoc] using
    congrArg (fun t ↦ t ≫ (ordinaryFinitePullback A v).map
      ((derivedUpperStarLowerStarAdjunction B f).counit.app M)) hh

private lemma comp_hom
    (A : Type (u + 1)) [CommRing A] {X P S : Scheme.{u}}
    (i : X ⟶ P) (q : P ⟶ S) (f : X ⟶ S) (hi : i ≫ q = f) :
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) i q f hi).hom =
      rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) i q f hi.symm := by
  subst f
  exact (conjugateEquiv_leftDerivedUpperStarComp_hom (ModuleCat.{u + 1} A)
    i q (i ≫ q) rfl).symm

private lemma inverse_pasting
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ O₄ O₅ : C}
    (c : O₀ ≅ O₁) (e : O₁ ≅ O₂) (s : O₂ ⟶ O₃)
    (b : O₄ ≅ O₃) (a : O₀ ≅ O₅) (w : O₅ ≅ O₄)
    (h : c.hom ≫ e.hom ≫ s = a.hom ≫ w.hom ≫ b.hom) :
    s ≫ b.inv ≫ w.inv = e.inv ≫ c.inv ≫ a.hom := by
  apply (cancel_epi e.hom).1
  apply (cancel_epi c.hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id, Category.id_comp] using
      congrArg (fun t ↦ t ≫ b.inv ≫ w.inv) h

private lemma supported_components
    {D E : Type*} [Category D] [Category E]
    {K L Y T Q R : D} (s : K ⟶ L) (pc : L ⟶ Y) (y : Y ⟶ T)
    (ηK : K ⟶ Q) (ηL : L ⟶ R) (gs : Q ⟶ R) (x : R ⟶ Y)
    (U : E ⥤ D) {M N P : E}
    (a : K ⟶ U.obj M) (b : Q ⟶ U.obj N)
    (v : M ⟶ N) (w : N ⟶ P) (t : U.obj P ⟶ T)
    (hc : pc = ηL ≫ x) (hn : s ≫ ηL = ηK ≫ gs)
    (ho : gs ≫ x ≫ y = b ≫ U.map w ≫ t)
    (hp : a ≫ U.map v = ηK ≫ b) :
    s ≫ pc ≫ y = a ≫ U.map (v ≫ w) ≫ t := by
  rw [hc]
  simp only [Category.assoc]
  rw [reassoc_of% hn, ho, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hp]

private theorem ordinary_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (M : DerivedCategoryModule A (ProjectiveLine S)) :
    (ordinaryFinitePushforward A (projection f false)).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
          (projectionSquare f i hi true).toCommSq).hom.app M) ≫
      (properExchange A (projectionSquare f i hi false)).inv.app
        ((ordinaryFinitePullback A (projectiveLineDiagonalProjection S true)).obj M) ≫
      (ordinaryFinitePullback A i.hom).map
        ((properExchange A (projectiveProjectionSquare S false)).inv.app M) =
    (CoordinateTrace.exchange1 A f ((ordinaryFinitePullback A i.hom).obj M)).inv ≫
      (ordinaryFinitePullback A f).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) i.hom
          (ProjectiveLine S ↘ S) f hi).inv.app
            ((ordinaryFinitePullback A i.hom).obj M) ≫
          (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
            ((pushPull A i).hom.app M)) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
        (ProjectiveLine S ↘ S) f hi.symm).hom.app
          ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj M) := by
  let B := ModuleCat.{u + 1} A
  let q := ProjectiveLine S ↘ S
  let w := productMap f i hi
  let p := projection f false
  let v := projection f true
  let v' := projectiveLineDiagonalProjection S true
  let sq := (projectiveProjectionSquare S false).toCommSq
  let sx : CommSq v p f f := (IsPullback.of_hasPullback f f).flip.toCommSq
  let si := (projectionSquare f i hi false).toCommSq
  have hv : w ≫ v' = v ≫ i.hom := (projectionSquare f i hi true).w
  let so : CommSq (w ≫ v') p q f := ⟨by
    rw [hv, Category.assoc, hi]
    exact sx.w⟩
  let cp := leftDerivedUpperStarComp B w v' (w ≫ v') rfl
  let ce := leftDerivedUpperStarComp B v i.hom (w ≫ v') hv
  let s := derivedSquareUpperStarIso B (projectionSquare f i hi true).toCommSq
  let c := (ordinaryFinitePushforward A q).mapIso ((pushPull A i).symm.app M) ≪≫
    (rightDerivedLowerStarCompOfEq B i.hom q f hi).app
      ((ordinaryFinitePullback A i.hom).obj M)
  have hu : (derivedUpperStarLowerStarAdjunction B i.hom).unit.app M =
      (pushPull A i).inv.app M := by
    apply (cancel_mono ((pushPull A i).hom.app M)).1
    rw [unit_comp_pushPull]
    simp
  have hc : c.hom = (ordinaryFinitePushforward A q).map
      ((derivedUpperStarLowerStarAdjunction B i.hom).unit.app M) ≫
        (rightDerivedLowerStarCompHom B i.hom q f hi.symm).app
          ((ordinaryFinitePullback A i.hom).obj M) := by
    simp only [c, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
      B, comp_hom, hu]
  have hs := source_exchange A so i.hom v f hv hi.symm sx M
  have hp := derivedBaseChangeMap_paste B sq si so rfl hi.symm M
  have hcancel : (ordinaryFinitePushforward A p).map (s.hom.app M) ≫
      (ordinaryFinitePushforward A p).map (cp.inv.app M) =
        (ordinaryFinitePushforward A p).map (ce.inv.app M) := by
    rw [← Functor.map_comp]
    congr 1
    simp only [s, cp, ce, B, w, v, v', derivedSquareUpperStarIso,
      Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hforward : (ordinaryFinitePullback A f).map c.hom ≫
      (derivedBaseChangeMap B sx).app ((ordinaryFinitePullback A i.hom).obj M) ≫
      (ordinaryFinitePushforward A p).map (s.hom.app M) =
    (leftDerivedUpperStarComp B i.hom q f hi.symm).hom.app
        ((ordinaryFinitePushforward A q).obj M) ≫
      (ordinaryFinitePullback A i.hom).map ((derivedBaseChangeMap B sq).app M) ≫
      (derivedBaseChangeMap B si).app ((ordinaryFinitePullback A v').obj M) := by
    apply (cancel_mono ((ordinaryFinitePushforward A p).map (cp.inv.app M))).1
    simp only [Category.assoc]
    rw [hcancel, hc]
    exact hs.trans hp.symm
  have h := inverse_pasting ((ordinaryFinitePullback A f).mapIso c)
    (CoordinateTrace.exchange1 A f ((ordinaryFinitePullback A i.hom).obj M))
    ((ordinaryFinitePushforward A p).map (s.hom.app M))
    ((properExchange A (projectionSquare f i hi false)).app
      ((ordinaryFinitePullback A v').obj M))
    ((leftDerivedUpperStarComp B i.hom q f hi.symm).app
      ((ordinaryFinitePushforward A q).obj M))
    ((ordinaryFinitePullback A i.hom).mapIso
      ((properExchange A (projectiveProjectionSquare S false)).app M))
    (by simpa only [Functor.mapIso_hom, Iso.app_hom, properExchange, asIso_hom,
      CoordinateTrace.exchange1] using hforward)
  simpa only [Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, Iso.trans_inv, Iso.symm_inv,
    c, B, q, w, p, v, v', s, projection, CoordinateTrace.pull, CoordinateTrace.push,
    ordinaryFinitePullback, ordinaryFinitePushforward] using h

set_option linter.auxLemma false in
attribute [local instance 1000000] projectionComparison._proof_1 productMap._proof_2

private theorem projection_false {S X : Scheme.{u}} (f : X ⟶ S) :
    projection f false = pullback.fst f f := rfl

private theorem projection_true {S X : Scheme.{u}} (f : X ⟶ S) :
    projection f true = pullback.snd f f := rfl

private theorem comparison_congr
    (A : Type (u + 1)) [CommRing A] {V X : Scheme.{u}}
    (p q : V ⟶ X) [IsProper p] [HasCompactification p]
    [IsProper q] [HasCompactification q] (h : p = q) :
    HEq (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) p)
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q) := by
  subst q
  rfl

private theorem shriek_congr
    (A : Type (u + 1)) [CommRing A] {V X : Scheme.{u}}
    (p q : V ⟶ X) [HasCompactification p] [HasCompactification q] (h : p = q) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) p =
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) q := by
  subst q
  rfl

-- Transfer whole functors and isomorphisms before taking components. This keeps
-- the selected compactifications and derived-category constructions folded.
private theorem inverse_transfer
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (F G : DerivedCategoryModule A (pullback f f) ⥤ DerivedCategoryModule A X)
    (T : DerivedCategoryModule A X ⥤ DerivedCategoryModule A (pullback f f))
    (hF : F = rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f f))
    (hG : G = (lowerStar (ModuleCat.{u + 1} A) (pullback.fst f f)).rightDerivedFunctor)
    (hT : T = ordinaryFinitePullback A (pullback.snd f f))
    (c : F ≅ G)
    (hc : HEq c (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) (pullback.fst f f)))
    (K : DerivedCategoryModule A X)
    (a : F.obj (T.obj K) ⟶ (ordinaryFinitePullback A f).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K))
    (ha : HEq a ((SfDiagonalKernel.exchangeFirst A f).inv.app K))
    (b : G.obj (T.obj K) ⟶ (ordinaryFinitePullback A f).obj
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K))
    (hb : HEq b (CoordinateTrace.exchange1 A f K).inv) :
    a ≫ (ordinaryFinitePullback A f).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom.app K) =
      c.hom.app (T.obj K) ≫ b := by
  subst F G T
  have hc' := eq_of_heq hc
  have ha' := eq_of_heq ha
  have hb' := eq_of_heq hb
  subst c a b
  exact (proper_self_exchange_forget_supports A f K).2

private theorem proper_inverse
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] (K : DerivedCategoryModule A X) :
    (SfDiagonalKernel.exchangeFirst A f).inv.app K ≫
      (ordinaryFinitePullback A f).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom.app K) =
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A)
      (projection f false)).hom.app ((ordinaryFinitePullback A (projection f true)).obj K) ≫
      (CoordinateTrace.exchange1 A f K).inv := by
  exact inverse_transfer A f
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f false))
    (lowerStar (ModuleCat.{u + 1} A) (projection f false)).rightDerivedFunctor
    (ordinaryFinitePullback A (projection f true))
    (shriek_congr A _ _ (projection_false f))
    (congrArg (fun p ↦ (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor)
      (projection_false f))
    (congrArg (fun p ↦ ordinaryFinitePullback A p) (projection_true f))
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A)
      (projection f false)) (comparison_congr A _ _ (projection_false f)) K
    ((SfDiagonalKernel.exchangeFirst A f).inv.app K) HEq.rfl
    (CoordinateTrace.exchange1 A f K).inv HEq.rfl

private lemma whisker_trans_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) {F G : D ⥤ E} {H : C ⥤ E}
    (c : F ≅ G) (e : J ⋙ G ≅ H) (K : C) :
    ((Functor.isoWhiskerLeft J c) ≪≫ e).hom.app K =
      c.hom.app (J.obj K) ≫ e.hom.app K := rfl

-- Expose the defining equality at the isomorphism level first: expanding its
-- component directly makes the kernel unfold the derived-category instances.
private theorem projection_factor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) (a : Bool) :
    projectionComparison A f i hi a =
      Functor.isoWhiskerLeft (ordinaryFinitePullback A (productMap f i hi))
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A)
          (projection f a)) ≪≫
      (properExchange A (projectionSquare f i hi a)).symm := by
  unfold projectionComparison
  rfl

private theorem projection_component
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (a : Bool) (K : DerivedCategoryModule A
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))) :
    (projectionComparison A f i hi a).hom.app K =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A)
        (projection f a)).hom.app ((ordinaryFinitePullback A (productMap f i hi)).obj K) ≫
      (properExchange A (projectionSquare f i hi a)).inv.app K := by
  rw [projection_factor]
  exact whisker_trans_app _ _ _ _

private theorem comparison_naturality
    (A : Type (u + 1)) [CommRing A] {V X : Scheme.{u}}
    (p : V ⟶ X) [IsProper p] [HasCompactification p]
    {K L : DerivedCategoryModule A V} (s : K ⟶ L) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map s ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) p).hom.app L =
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) p).hom.app K ≫
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map s := by
  exact (rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) p).hom.naturality s

/-- Exchange pasting for an arbitrary complex on the projective line.

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the composition isomorphism and canonical pullback
counits in the first-coordinate calculation.
(auxiliary; not a blueprint node).

Proof: Write q:P -> S, W = P times_S P, V = X times_S X and w = i times_S i.
The two projection squares for w commute. Expand projectionComparison as proper
forget-supports followed by inverse ordinary exchange. Proper forget-supports
intertwines ordinary and supported exchange: expand the chosen-compactification
exchange, use the compactification-refinement comparison followed by its
forget-supports map, and then the open-immersion comparison with ordinary direct
image. Thus it suffices to compare ordinary exchange on the two self-products.
Transpose the comparison by the adjunction for V -> X. The defining mate equation
replaces exchange followed by this counit by the pullback square comparison
followed by pullback of the counit for f. Expand the direct-image compositor
using its conjugate pullback compositor. Its counit is the composite counit for
i followed by q. Naturality moves these counits through the pullback square
comparisons. Pullback-composition associativity and w followed by either
projection equal to the corresponding projection followed by i identify the two
remaining square maps. The unit and counit for i cancel. The resulting
cancellation is pushPull: identify Ri_* with L(i inverse)^* by the exact
inverse-image/direct-image comparison, then use i inverse followed by i = id.
This is precisely the definition of pushPull, including its identity compositor.
Undoing the transpose gives the displayed equality. No twist, coefficient
normalization, trace map or constant-object comparison enters this argument;
the object M is arbitrary. Empty schemes and zero coefficients require no
additional assumptions. -/
theorem exchangeIsoTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (M : DerivedCategoryModule A (ProjectiveLine S)) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f false)).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
          (projectionSquare f i hi true).toCommSq).hom.app M) ≫
      (projectionComparison A f i hi false).hom.app
        ((ordinaryFinitePullback A
          (projectiveLineDiagonalProjection S true)).obj M) ≫
      (ordinaryFinitePullback A i.hom).map
        ((properExchange A (projectiveProjectionSquare S false)).inv.app M) =
    (SfDiagonalKernel.exchangeFirst A f).inv.app
        ((ordinaryFinitePullback A i.hom).obj M) ≫
      (ordinaryFinitePullback A f).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom.app
            ((ordinaryFinitePullback A i.hom).obj M) ≫
          (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) i.hom
            (ProjectiveLine S ↘ S) f hi).inv.app
              ((ordinaryFinitePullback A i.hom).obj M) ≫
          (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
            ((pushPull A i).hom.app M)) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
        (ProjectiveLine S ↘ S) f hi.symm).hom.app
          ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj M) := by
  refine supported_components
    (D := DerivedCategoryModule A X) (E := DerivedCategoryModule A S)
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f false)).map
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (projectionSquare f i hi true).toCommSq).hom.app M))
    ((projectionComparison A f i hi false).hom.app
      ((ordinaryFinitePullback A (projectiveLineDiagonalProjection S true)).obj M))
    ((ordinaryFinitePullback A i.hom).map
      ((properExchange A (projectiveProjectionSquare S false)).inv.app M))
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A)
        (projection f false)).hom.app
        ((ordinaryFinitePullback A (projection f true)).obj
          ((ordinaryFinitePullback A i.hom).obj M)))
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A)
        (projection f false)).hom.app
        ((ordinaryFinitePullback A (productMap f i hi)).obj
          ((ordinaryFinitePullback A (projectiveLineDiagonalProjection S true)).obj M)))
    ((lowerStar (ModuleCat.{u + 1} A) (projection f false)).rightDerivedFunctor.map
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (projectionSquare f i hi true).toCommSq).hom.app M))
    ((properExchange A (projectionSquare f i hi false)).inv.app
      ((ordinaryFinitePullback A (projectiveLineDiagonalProjection S true)).obj M))
    (ordinaryFinitePullback A f)
    ((SfDiagonalKernel.exchangeFirst A f).inv.app
      ((ordinaryFinitePullback A i.hom).obj M))
    ((CoordinateTrace.exchange1 A f ((ordinaryFinitePullback A i.hom).obj M)).inv)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom.app
      ((ordinaryFinitePullback A i.hom).obj M))
    ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) i.hom
      (ProjectiveLine S ↘ S) f hi).inv.app ((ordinaryFinitePullback A i.hom).obj M) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
        ((pushPull A i).hom.app M))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
      (ProjectiveLine S ↘ S) f hi.symm).hom.app
        ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj M))
    ?_ ?_ ?_ ?_
  · exact projection_component A f i hi false _
  · exact comparison_naturality A (projection f false)
      (K := (ordinaryFinitePullback A (projection f true)).obj
        ((ordinaryFinitePullback A i.hom).obj M))
      (L := (ordinaryFinitePullback A (productMap f i hi)).obj
        ((ordinaryFinitePullback A (projectiveLineDiagonalProjection S true)).obj M)) _
  · simpa only [ordinaryFinitePushforward] using ordinary_transport A f i hi M
  · exact proper_inverse A f ((ordinaryFinitePullback A i.hom).obj M)

end AlgebraicGeometry.Etale.SfP1Transport
