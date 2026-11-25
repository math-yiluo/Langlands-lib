/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1ChartExchange
public import WeilConjectures.AlgebraicGeometry.SfP1CoordinateLineComparison
import WeilConjectures.AlgebraicGeometry.SfIsoPushPullUnitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange

/-! # Exchange under a projective-line presentation -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

/-- The fixed second projection gives the same compact-support functor.
Source: the definition of projection.
Proof: reduce the true branch; the compactification existence proofs agree by
proof irrelevance. (auxiliary; not a blueprint node). -/
theorem secondProjectionShriek_eq
    (A : Type (u + 1)) [CommRing A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f true) =
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f) := by
  unfold projection
  rfl

attribute [local semireducible] projection
attribute [local implicit_reducible] projection

/-- The fixed-projection functor transport is the identity on every complex.
Source: secondProjectionShriek_eq and projection.
Proof: the functors become identical in the true branch, so eqToHom is the
identity natural transformation, whose components are identity morphisms.
(auxiliary; not a blueprint node). -/
theorem secondProjectionShriek_hom_app
    (A : Type (u + 1)) [CommRing A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (B : DerivedCategoryModule A (pullback f f)) :
    (eqToIso (secondProjectionShriek_eq A f)).hom.app B =
      𝟙 ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).obj B) := by
  rw [eqToIso.hom, eqToHom_refl, NatTrans.id_app]
  unfold projection
  rfl

/-- The second projection comparison with a fixed, reduced source functor.
Source: projectionComparison (auxiliary; not a blueprint node). -/
@[irreducible]
def secondProjectionComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) :
    ordinaryFinitePullback A (productMap f i hi) ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f) ≅
      ordinaryFinitePushforward A (projectiveLineDiagonalProjection S true) ⋙
        ordinaryFinitePullback A i.hom :=
  Functor.isoWhiskerLeft _ (eqToIso (secondProjectionShriek_eq A f)).symm ≪≫
    projectionComparison A f i hi true

section ExchangeProofHelpers

attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [local instance 2000] Abelian.toPreadditive

-- Typed forms of the existing private argument in ProperSelfExchangeForgetSupports.
attribute [local irreducible] instCategoryDerivedCategory
  rightDerivedLowerShriekBaseChangeMap rightDerivedLowerShriekIsoRightDerivedLowerStar

private theorem proper_hom_app
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K =
      R(((HasCompactification.compactification q).g)_*[ModuleCat.{u + 1} A]).map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
          (HasCompactification.compactification q).i).app K) ≫
      (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A)
        (HasCompactification.compactification q).i
        (HasCompactification.compactification q).g q
        (HasCompactification.compactification q).comm).app K := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
    rightDerivedLowerShriekToLowerStarComp_comp_eq]
  rfl

attribute [local irreducible] rightDerivedLowerShriekOfCompactificationIso

private theorem proper_compactification_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    [QuasiCompact q] (c : Compactification q) (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekIso A c).hom.app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K =
      R((c.g)_*[ModuleCat.{u + 1} A]).map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app K) ≫
      (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) c.i c.g q c.comm).app K := by
  exact (congrArg (fun z ↦ (rightDerivedLowerShriekIso A c).hom.app K ≫ z)
    (proper_hom_app A q K)).trans
      (rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar
        A c (HasCompactification.compactification q) K)

private theorem raw_exchange_combined
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' q' q g)
    (c : Compactification q) (c' : Compactification q') (h : c'.Z ⟶ c.Z)
    (hi : IsPullback g' c'.i c.i h) (hp : CommSq h c'.g c.g g)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
        c c' h hi hp).app K ≫
      R((c'.g)_*[ModuleCat.{u + 1} A]).map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c'.i).app
          (L((g')^*[ModuleCat.{u + 1} A]).obj K)) ≫
      (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) c'.i c'.g q' c'.comm).app
        (L((g')^*[ModuleCat.{u + 1} A]).obj K) =
    L((g)^*[ModuleCat.{u + 1} A]).map
      (R((c.g)_*[ModuleCat.{u + 1} A]).map
        ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app K) ≫
        (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) c.i c.g q c.comm).app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K := by
  exact (rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app_comp_toLowerStar
    (ModuleCat.{u + 1} A) sq c c' h hi hp K).trans
    (CategoryTheory.Functor.map_comp_assoc L((g)^*[ModuleCat.{u + 1} A]) _ _ _).symm

private theorem exchange_of_forget
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K₀ K₁ : C} {T₀ T₁ T₂ T₃ : D}
    (a : F.obj K₀ ⟶ T₀) (b : T₀ ⟶ T₁) (p : T₁ ⟶ T₃)
    (f : T₀ ⟶ T₂) (g : T₂ ⟶ T₃) (d s : K₀ ⟶ K₁)
    (e : F.obj K₁ ⟶ T₃)
    (hi : b ≫ p = f ≫ g) (hb : a ≫ f ≫ g = F.map s ≫ e) (hq : d = s) :
    a ≫ b ≫ p = F.map d ≫ e := by
  rw [hi, hb, hq]

private theorem comp_whisker_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {P : C ⥤ E} {J : C ⥤ D} {Q Q' : D ⥤ E}
    (a : P ⟶ J ⋙ Q) (b : Q ⟶ Q') (K : C) :
    (a ≫ Functor.whiskerLeft J b).app K = a.app K ≫ b.app (J.obj K) := rfl

attribute [local irreducible] rightDerivedLowerShriekBaseChangeMap'

private theorem primed_exchange_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [HasCompactification q'] [QuasiCompact q']
    (c : Compactification q) (c' : Compactification q') (h : c'.Z ⟶ c.Z)
    (hi : IsPullback g' c'.i c.i h) (hp : CommSq h c'.g c.g g)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekBaseChangeMap' A c c' h hi hp).app K =
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
        c c' h hi hp).app K ≫
      (rightDerivedLowerShriekIso A c').hom.app (L((g')^*[ModuleCat.{u + 1} A]).obj K) := by
  simpa only [rightDerivedLowerShriekBaseChangeMap'] using
    comp_whisker_app
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
        c c' h hi hp) (rightDerivedLowerShriekIso A c').hom K

private theorem proper_exchange_raw
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (c' : Compactification q')
    (h : c'.Z ⟶ (HasCompactification.compactification q).Z)
    (hi : IsPullback g' c'.i (HasCompactification.compactification q).i h)
    (hp : CommSq h c'.g (HasCompactification.compactification q).g g)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
        (HasCompactification.compactification q) c' h hi hp).app K ≫
      (rightDerivedLowerShriekIso A c').hom.app (L((g')^*[ModuleCat.{u + 1} A]).obj K) ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q').hom.app
        (L((g')^*[ModuleCat.{u + 1} A]).obj K) =
    L((g)^*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K := by
  exact exchange_of_forget L((g)^*[ModuleCat.{u + 1} A]) _ _ _ _ _ _ _ _
    (proper_compactification_hom A q' c' (L((g')^*[ModuleCat.{u + 1} A]).obj K))
    (raw_exchange_combined A sq (HasCompactification.compactification q) c' h hi hp K)
    (proper_hom_app A q K)

private theorem replace_first
    {C : Type*} [Category C] {V₀ V₁ V₂ V₃ : C}
    (a : V₀ ⟶ V₂) (d : V₀ ⟶ V₁) (b : V₁ ⟶ V₂) (c : V₂ ⟶ V₃)
    (t : V₀ ⟶ V₃) (h : a = d ≫ b) (H : d ≫ b ≫ c = t) : a ≫ c = t := by
  rw [h, Category.assoc]
  exact H

private theorem proper_exchange_compactification
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (c' : Compactification q')
    (h : c'.Z ⟶ (HasCompactification.compactification q).Z)
    (hi : IsPullback g' c'.i (HasCompactification.compactification q).i h)
    (hp : CommSq h c'.g (HasCompactification.compactification q).g g)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekBaseChangeMap' A (HasCompactification.compactification q)
        c' h hi hp).app K ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q').hom.app
        (L((g')^*[ModuleCat.{u + 1} A]).obj K) =
    L((g)^*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K := by
  exact replace_first
    ((rightDerivedLowerShriekBaseChangeMap' A (HasCompactification.compactification q)
      c' h hi hp).app K)
    ((rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
      (HasCompactification.compactification q) c' h hi hp).app K)
    ((rightDerivedLowerShriekIso A c').hom.app (L((g')^*[ModuleCat.{u + 1} A]).obj K))
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q').hom.app
      (L((g')^*[ModuleCat.{u + 1} A]).obj K))
    (L((g)^*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K)
    (primed_exchange_app A (HasCompactification.compactification q) c' h hi hp K)
    (proper_exchange_raw A sq c' h hi hp K)

private theorem replace_arrow
    {C : Type*} [Category C] {V₀ V₁ V₂ : C}
    (a a' : V₀ ⟶ V₁) (c : V₁ ⟶ V₂) (t : V₀ ⟶ V₂)
    (h : a = a') (H : a' ≫ c = t) : a ≫ c = t := by
  rw [h]
  exact H

private theorem proper_exchange_raw_model
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q').hom.app (L((g')^*[ModuleCat.{u + 1} A]).obj K) =
      L((g)^*[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) q).hom.app K) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K := by
  have h₀ := NatTrans.congr_app (rightDerivedLowerShriekBaseChangeMap_eq A sq) K
  have H := proper_exchange_compactification A sq.toCommSq
    ((HasCompactification.compactification q).ofIsPullback sq)
    (pullback.fst (HasCompactification.compactification q).g g)
    ((HasCompactification.compactification q).isPullback_i_ofIsPullback sq)
    (IsPullback.of_hasPullback (HasCompactification.compactification q).g g).toCommSq K
  exact replace_arrow ((rightDerivedLowerShriekBaseChangeMap A sq).app K)
    ((rightDerivedLowerShriekBaseChangeMap' A (HasCompactification.compactification q)
      ((HasCompactification.compactification q).ofIsPullback sq)
      (pullback.fst (HasCompactification.compactification q).g g)
      ((HasCompactification.compactification q).isPullback_i_ofIsPullback sq)
      (IsPullback.of_hasPullback (HasCompactification.compactification q).g g).toCommSq).app K)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q').hom.app
      (L((g')^*[ModuleCat.{u + 1} A]).obj K))
    (L((g)^*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K) h₀ H

private theorem compHom_eq
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) :
    rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) a b c h.symm =
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) a b c h).hom := by
  subst c
  rw [rightDerivedLowerStarCompHom, conjugateEquiv_leftDerivedUpperStarComp_hom]
  rfl

private theorem over_base_square
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) (sq : CommSq a c b (𝟙 Z))
    (K : DerivedCategoryModule A Z) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app K =
      (ordinaryFinitePullback A c).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) Z).hom.app K) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a b c h.symm).hom.app K := by
  subst c
  have hid := leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) (a ≫ b) K
  have hid' :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (a ≫ b) (𝟙 Z) (a ≫ b)
        (Category.comp_id _).symm).inv.app K =
      (ordinaryFinitePullback A (a ≫ b)).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) Z).hom.app K) := by
    rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (a ≫ b) (𝟙 Z)
      (a ≫ b) (Category.comp_id _).symm).hom.app K), Iso.hom_inv_id_app]
    exact hid.symm
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [hid']

private theorem over_base_exchange
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) (sq : CommSq a c b (𝟙 Z))
    (B : DerivedCategoryModule A Y) :
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app B =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) Z).hom.app
          ((ordinaryFinitePushforward A b).obj B) ≫
        (ordinaryFinitePushforward A b).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a).unit.app B) ≫
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) a b c h).hom.app
          ((ordinaryFinitePullback A a).obj B) := by
  rw [← compHom_eq A a b c h]
  apply ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c).homEquiv _ _).symm.injective
  dsimp only [ordinaryFinitePullback, ordinaryFinitePushforward]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [derivedUpperStar_map_derivedBaseChangeMap_app_counit,
    map_rightDerivedLowerStarCompHom_app_counit]
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a b c h.symm).hom.naturality
    ((ordinaryFinitePushforward A b).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a).unit.app B))
  dsimp only [Functor.comp_map, ordinaryFinitePullback, ordinaryFinitePushforward] at hn
  rw [reassoc_of% hn, ← Functor.map_comp_assoc]
  have hc := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b).counit.naturality
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a).unit.app B)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hc
  rw [hc, Functor.map_comp, Category.assoc,
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a).left_triangle_components,
    Category.comp_id]
  rw [over_base_square A a b c h sq, Category.assoc]
  rfl

private theorem over_base_trace
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (sq : CommSq i.hom f (ProjectiveLine S ↘ S) (𝟙 S))
    (B : DerivedCategoryModule A (ProjectiveLine S)) :
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app B ≫
        presentationTrace A f i hi B =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app
        ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj B) := by
  rw [over_base_exchange A i.hom (ProjectiveLine S ↘ S) f hi sq B]
  unfold presentationTrace
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    unit_comp_pushPull, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

private theorem ordinary_presentation_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (B : DerivedCategoryModule A (ProjectiveLine S)) :
    (properExchange A (projectionSquare f i hi true)).inv.app
        ((ordinaryFinitePullback A (projectiveLineDiagonalProjection S false)).obj B) ≫
      (ordinaryFinitePullback A i.hom).map
        ((properExchange A (projectiveProjectionSquare S true)).inv.app B) =
    (ordinaryFinitePushforward A (projection f true)).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
          (firstProjectionSquare f i hi).toCommSq).inv.app B) ≫
      (properExchange A (IsPullback.of_hasPullback f f)).inv.app
        ((ordinaryFinitePullback A i.hom).obj B) ≫
      (ordinaryFinitePullback A f).map (presentationTrace A f i hi B) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
        (ProjectiveLine S ↘ S) f hi.symm).hom.app
          ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj B) := by
  let sq : CommSq i.hom f (ProjectiveLine S ↘ S) (𝟙 S) :=
    CommSq.mk (by simpa using hi)
  have h := derivedBaseChangeMap_cube (ModuleCat.{u + 1} A)
    (projectiveProjectionSquare S true).toCommSq sq
    (projectionSquare f i hi true).toCommSq (IsPullback.of_hasPullback f f).toCommSq
    sq (firstProjectionSquare f i hi).toCommSq B
  have ht := over_base_trace A f i hi sq B
  have hs := over_base_square A i.hom (ProjectiveLine S ↘ S) f hi sq
    ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj B)
  have h' :
      (ordinaryFinitePullback A i.hom).map
        ((properExchange A (projectiveProjectionSquare S true)).hom.app B) ≫
      (properExchange A (projectionSquare f i hi true)).hom.app
        ((ordinaryFinitePullback A (projectiveLineDiagonalProjection S false)).obj B) ≫
      (ordinaryFinitePushforward A (projection f true)).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
          (firstProjectionSquare f i hi).toCommSq).inv.app B) =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app
        ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj B) ≫
      (ordinaryFinitePullback A f).map
        ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app B) ≫
      (properExchange A (IsPullback.of_hasPullback f f)).hom.app
        ((ordinaryFinitePullback A i.hom).obj B) := by
    dsimp only [Bool.not] at h
    simpa only [properExchange, asIso_hom, projection, Bool.not_true,
      ordinaryFinitePullback, ordinaryFinitePushforward] using h
  apply (cancel_epi
    ((ordinaryFinitePullback A i.hom).map
        ((properExchange A (projectiveProjectionSquare S true)).hom.app B) ≫
      (properExchange A (projectionSquare f i hi true)).hom.app
        ((ordinaryFinitePullback A (projectiveLineDiagonalProjection S false)).obj B))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% h', Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, ht]
  rw [← hs, Iso.inv_hom_id_app]
  rfl

set_option linter.auxLemma false in
attribute [local instance 1000000] projectionComparison._proof_1 productMap._proof_2

attribute [local implicit_reducible] projectiveLineDiagonalProjection

attribute [local irreducible] upperStar lowerStar rightDerivedLowerShriek

-- Normalize comparison isomorphisms before taking components.
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

private theorem second_factor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) :
    secondProjectionComparison A f i hi =
      Functor.isoWhiskerLeft (ordinaryFinitePullback A (productMap f i hi))
        (eqToIso (secondProjectionShriek_eq A f)).symm ≪≫
        projectionComparison A f i hi true := by
  unfold secondProjectionComparison
  rfl

private theorem comparison_congr
    (A : Type (u + 1)) [CommRing A] {V X : Scheme.{u}}
    (p q : V ⟶ X) [IsProper p] [HasCompactification p]
    [IsProper q] [HasCompactification q] (h : p = q) :
    HEq (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) p)
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q) := by
  subst q
  rfl

private theorem transport_iso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) {R R' S : D ⥤ E} {T : C ⥤ E} (h : R = R')
    (c : R ≅ S) (c' : R' ≅ S) (hc : HEq c c') (b : J ⋙ S ≅ T) :
    Functor.isoWhiskerLeft J (eqToIso h).symm ≪≫
        (Functor.isoWhiskerLeft J c ≪≫ b) =
      Functor.isoWhiskerLeft J c' ≪≫ b := by
  subst R'
  have hc' := eq_of_heq hc
  subst c'
  simp

private theorem second_normalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) :
    secondProjectionComparison A f i hi =
      Functor.isoWhiskerLeft (ordinaryFinitePullback A (productMap f i hi))
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (pullback.snd f f)) ≪≫
      (properExchange A (projectionSquare f i hi true)).symm := by
  rw [second_factor, projection_factor]
  exact transport_iso _ (secondProjectionShriek_eq A f) _ _
    (comparison_congr A (projection f true) (pullback.snd f f) rfl) _

private theorem inverse_exchange
    {C : Type*} [Category C] {W X Y Z : C}
    (β : W ≅ X) (E : Y ≅ Z) (c : W ⟶ Y) (c' : X ⟶ Z)
    (h : β.hom ≫ c' = c ≫ E.hom) : β.inv ≫ c = c' ≫ E.inv := by
  rw [← cancel_epi β.hom, Iso.hom_inv_id_assoc,
    ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

-- Keep the final cancellation abstract so no derived-functor data is unfolded.
private theorem forget_pasting
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : E ⥤ D) (R R' : C ⥤ D) (z : R ≅ R')
    {U V : C} {W W' T : E} {J : D}
    (e : F.obj W ≅ R.obj V) (d : F.obj W' ≅ R'.obj V)
    (a : W ⟶ W') (s : U ⟶ V) (t : W' ⟶ T) (c : F.obj T ⟶ J)
    (χ : R'.obj U ⟶ J)
    (he : e.hom ≫ z.hom.app V = F.map a ≫ d.hom)
    (hχ : χ = R'.map s ≫ d.inv ≫ F.map t ≫ c) :
    z.hom.app U ≫ χ = R.map s ≫ e.inv ≫ F.map (a ≫ t) ≫ c := by
  have h := inverse_exchange e d (F.map a) (z.hom.app V) he
  rw [hχ, ← z.hom.naturality_assoc, ← reassoc_of% h]
  simp only [Functor.map_comp, Category.assoc]

private theorem presentation_pasting
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : E ⥤ D) (R R' : C ⥤ D) (z : R ≅ R')
    {U V : C} {W W' T : E} {J J₀ : D}
    (e : F.obj W ≅ R.obj V) (d : F.obj W' ≅ R'.obj V)
    (a : W ⟶ W') (s : U ⟶ V) (t : W' ⟶ T) (c : F.obj T ⟶ J)
    (b : R.obj U ⟶ J₀) (b' : R'.obj U ⟶ J₀) (l : J₀ ⟶ J)
    (he : e.hom ≫ z.hom.app V = F.map a ≫ d.hom)
    (hb : b = z.hom.app U ≫ b')
    (hχ : b' ≫ l = R'.map s ≫ d.inv ≫ F.map t ≫ c) :
    b ≫ l = R.map s ≫ e.inv ≫ F.map (a ≫ t) ≫ c := by
  rw [hb, Category.assoc]
  exact forget_pasting F R R' z e d a s t c (b' ≫ l) he hχ

private theorem family_pasting
    {C D E H W : Type*}
    [Category C] [Category D] [Category E] [Category H] [Category W]
    (F : E ⥤ D) (G : H ⥤ C) (T T' : H ⥤ E) (R R' : C ⥤ D)
    (z : R ≅ R') (zf : T ≅ T') (e : T ⋙ F ≅ G ⋙ R) (d : T' ⋙ F ≅ G ⋙ R')
    (he : e.hom ≫ Functor.whiskerLeft G z.hom =
      Functor.whiskerRight zf.hom F ≫ d.hom)
    (J₁ : W ⥤ C) (Q : W ⥤ D) (b : J₁ ⋙ R ≅ Q) (b' : J₁ ⋙ R' ≅ Q)
    (hb : b = Functor.isoWhiskerLeft J₁ z ≪≫ b')
    (K : H) (B : W) {T₀ : E} {J : D}
    (s : J₁.obj B ⟶ G.obj K) (t : T'.obj K ⟶ T₀) (c : F.obj T₀ ⟶ J)
    (l : Q.obj B ⟶ J)
    (hχ : b'.hom.app B ≫ l = R'.map s ≫ d.inv.app K ≫ F.map t ≫ c) :
    b.hom.app B ≫ l = R.map s ≫ e.inv.app K ≫ F.map (zf.hom.app K ≫ t) ≫ c := by
  apply presentation_pasting F R R' z (e.app K) (d.app K)
    (zf.hom.app K) s t c (b.hom.app B) (b'.hom.app B) l _ _ hχ
  · exact congrArg (fun α ↦ α.app K) he
  · rw [hb]
    rfl

attribute [local irreducible] TraceDiagonalDatum.baseChangeIso

-- Expose the two hom equalities before evaluating their components.
private theorem supported_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    (TraceDiagonalDatum.baseChangeIso (Λ := A) f).hom =
      rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f f) := by
  unfold TraceDiagonalDatum.baseChangeIso
  rfl

private theorem ordinary_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    (properExchange A (IsPullback.of_hasPullback f f)).hom =
      derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback f f).toCommSq := by
  unfold properExchange
  rfl

private theorem raw_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f f) ≫
        Functor.whiskerLeft L((pullback.fst f f)^*[ModuleCat.{u + 1} A])
          (rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) (pullback.snd f f)).hom =
      Functor.whiskerRight
          (rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) f).hom L((f)^*[ModuleCat.{u + 1} A]) ≫
        derivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback f f).toCommSq := by
  ext K
  exact proper_exchange_raw_model A (IsPullback.of_hasPullback f f) K

private theorem supported_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    (TraceDiagonalDatum.baseChangeIso (Λ := A) f).hom ≫
        Functor.whiskerLeft L((pullback.fst f f)^*[ModuleCat.{u + 1} A])
          (rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) (pullback.snd f f)).hom =
      Functor.whiskerRight
          (rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) f).hom L((f)^*[ModuleCat.{u + 1} A]) ≫
        (properExchange A (IsPullback.of_hasPullback f f)).hom := by
  rw [supported_hom, ordinary_hom]
  exact raw_naturality A f

-- Fix the functors before specializing the derived complexes.
set_option linter.defProp false in
@[irreducible] private def categorical_presentation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) :=
  @family_pasting
    (DerivedCategoryModule A (pullback f f))
    (DerivedCategoryModule A X) (DerivedCategoryModule A S)
    (DerivedCategoryModule A X)
    (DerivedCategoryModule A
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))) _ _ _ _ _
    L((f)^*[ModuleCat.{u + 1} A])
    L((pullback.fst f f)^*[ModuleCat.{u + 1} A])
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (ordinaryFinitePushforward A f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f))
    (ordinaryFinitePushforward A (pullback.snd f f))
    (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) (pullback.snd f f))
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f)
    (TraceDiagonalDatum.baseChangeIso (Λ := A) f)
    (properExchange A (IsPullback.of_hasPullback f f))
    (supported_naturality A f)
    (ordinaryFinitePullback A (productMap f i hi))
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S true) ⋙
      ordinaryFinitePullback A i.hom)
    (secondProjectionComparison A f i hi)
    (properExchange A (projectionSquare f i hi true)).symm
    (second_normalized A f i hi)

set_option linter.defProp false in
@[irreducible] private def raw_geometry
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (B : DerivedCategoryModule A (ProjectiveLine S)) :=
  let K : DerivedCategoryModule A X := (ordinaryFinitePullback A i.hom).obj B
  let σ := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
    (firstProjectionSquare f i hi).toCommSq).inv.app B
  categorical_presentation A f i hi K
    ((ordinaryFinitePullback A (projectiveLineDiagonalProjection S false)).obj B)
    σ (presentationTrace A f i hi B)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
      (ProjectiveLine S ↘ S) f hi.symm).hom.app
        ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj B))
    ((ordinaryFinitePullback A i.hom).map
      ((properExchange A (projectiveProjectionSquare S true)).inv.app B))

set_option linter.defProp false in
@[irreducible] private def raw_presentation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (B : DerivedCategoryModule A (ProjectiveLine S)) :=
  raw_geometry A f i hi B (ordinary_presentation_exchange A f i hi B)

/-- Exchange along the presentation isomorphism, before inserting any coefficient
comparison or trace.

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the paragraph identifying the second coordinate
integral using composition of direct images and the same pullback counits.
(auxiliary; not a blueprint node)

Proof: replace the compact-support projection by ordinary direct image using
proper forget-supports. This comparison intertwines exchange: evaluate the
compactification base-change/forget-supports equation at B and cancel its
invertible factors. Concretely use rightDerivedLowerShriekBaseChangeMap_eq, the
compactification base-change/forget-supports equation, and the hom-component
formula for rightDerivedLowerShriekIsoRightDerivedLowerStar.
For ordinary direct images, compute the square i;q=f over the identity base by
transposing along the adjunction for f. The composite counit formula and naturality
reduce this computation to inverse-image composition coherence. Then use
derivedBaseChangeMap_cube to paste the projection squares induced by i with the
self-product square of q. The horizontal equivalence i identifies pushPull with the inverse of the
unit of the pullback/direct-image adjunction for i. This follows by the triangle
identities and the inverse-morphism comparison.
Cancel the product exchange isomorphisms and apply the direct-image composition
comparison for i;q=f. This gives exactly the displayed equation. B is arbitrary;
no Tate comparison, trace, splitting, or nonempty-scheme assumption is used. -/
theorem presentationExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (B : DerivedCategoryModule A (ProjectiveLine S)) :
    (secondProjectionComparison A f i hi).hom.app
        ((ordinaryFinitePullback A (projectiveLineDiagonalProjection S false)).obj B) ≫
      (ordinaryFinitePullback A i.hom).map
        ((properExchange A (projectiveProjectionSquare S true)).inv.app B) =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
          (firstProjectionSquare f i hi).toCommSq).inv.app B) ≫
      (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app
        ((ordinaryFinitePullback A i.hom).obj B) ≫
      (ordinaryFinitePullback A f).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) f).hom.app
            ((ordinaryFinitePullback A i.hom).obj B) ≫
          presentationTrace A f i hi B) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
        (ProjectiveLine S ↘ S) f hi.symm).hom.app
          ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj B) := by
  exact raw_presentation A f i hi B

end ExchangeProofHelpers

end AlgebraicGeometry.Etale.SfP1Transport
