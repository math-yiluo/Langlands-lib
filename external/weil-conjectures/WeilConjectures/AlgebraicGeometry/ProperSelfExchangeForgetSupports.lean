/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange

/-! # Proper self-product exchange and forget supports

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-geo-p1-adjunction/thm-amb-p1-adjunction.proof.md, first triangle, the exchange
obtained from the same pullback counits on the Cartesian square.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

open scoped CategoryTheory.Functor

-- The typed comparison helpers follow the proved proper-comparison calculation in
-- WeilConjectures.SixFunctors.ProjectiveLinePresentedTraceExchange. Explicit interfaces prevent
-- elaboration from unfolding the unbounded derived-category constructions.

set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local instance 20000] Etale.sheafBraidedCategory

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  rightDerivedLowerShriekBaseChangeMap rightDerivedLowerShriekIsoRightDerivedLowerStar

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.leftDerivedFunctor

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

-- Convert category aliases before specializing the functors or their comparison maps.
private theorem proper_exchange_transport_raw
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q']
    (F : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (H S : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (H' S' : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : F = L((g)^*[ModuleCat.{u + 1} A]))
    (hG : G = L((g')^*[ModuleCat.{u + 1} A]))
    (hH : H = R(q)_![ModuleCat.{u + 1} A])
    (hH' : H' = R(q')_![ModuleCat.{u + 1} A])
    (hS : S = R((q)_*[ModuleCat.{u + 1} A]))
    (hS' : S' = R((q')_*[ModuleCat.{u + 1} A]))
    (η : H ≅ S) (η' : H' ≅ S')
    (hη : HEq η (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q))
    (hη' : HEq η' (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q'))
    (β : H ⋙ F ⟶ G ⋙ H') (βs : S ⋙ F ⟶ G ⋙ S')
    (hb : HEq β (rightDerivedLowerShriekBaseChangeMap A sq))
    (hbs : HEq βs (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq))
    (K : DerivedCategoryModule A X) :
    β.app K ≫ η'.hom.app (G.obj K) = F.map (η.hom.app K) ≫ βs.app K := by
  subst F G H H' S S'
  have he := eq_of_heq hη
  have he' := eq_of_heq hη'
  have hb' := eq_of_heq hb
  have hbs' := eq_of_heq hbs
  subst η η' β βs
  exact proper_exchange_raw_model A sq K

private theorem proper_exchange_transport_ordinary
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q']
    (F : DerivedCategoryModule A Y ⥤
      DerivedCategoryModule A Y') (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A X')
    (H S : DerivedCategoryModule A X ⥤
      DerivedCategoryModule A Y) (H' S' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A Y')
    (hF : F = L((g)^*[ModuleCat.{u + 1} A]))
    (hG : G = L((g')^*[ModuleCat.{u + 1} A]))
    (hH : H = R(q)_![ModuleCat.{u + 1} A])
    (hH' : H' = R(q')_![ModuleCat.{u + 1} A])
    (hS : S = R((q)_*[ModuleCat.{u + 1} A]))
    (hS' : S' = R((q')_*[ModuleCat.{u + 1} A]))
    (η : H ≅ S) (η' : H' ≅ S')
    (hη : HEq η (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q))
    (hη' : HEq η' (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q'))
    (β : H ⋙ F ⟶ G ⋙ H') (βs : S ⋙ F ⟶ G ⋙ S')
    (hb : HEq β (rightDerivedLowerShriekBaseChangeMap A sq))
    (hbs : HEq βs (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq))
    (K : DerivedCategoryModule A X) :
    β.app K ≫ η'.hom.app (G.obj K) = F.map (η.hom.app K) ≫ βs.app K := by
  exact proper_exchange_transport_raw A sq F G H S H' S'
    hF hG hH hH' hS hS' η η' hη hη' β βs hb hbs K

private theorem proper_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q').hom.app ((ordinaryFinitePullback A g').obj K) =
      (ordinaryFinitePullback A g).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) q).hom.app K) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K := by
  exact proper_exchange_transport_ordinary A sq
    (ordinaryFinitePullback A g) (ordinaryFinitePullback A g')
    R(q)_![ModuleCat.{u + 1} A] R((q)_*[ModuleCat.{u + 1} A])
    R(q')_![ModuleCat.{u + 1} A] R((q')_*[ModuleCat.{u + 1} A])
    rfl rfl rfl rfl rfl rfl
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q')
    HEq.rfl HEq.rfl (rightDerivedLowerShriekBaseChangeMap A sq)
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq) HEq.rfl HEq.rfl K

private lemma inverse_exchange
    {C : Type*} [Category C] {W X Y Z : C}
    (β : W ⟶ X) (βinv : X ⟶ W) (E : Y ⟶ Z) (Einv : Z ⟶ Y)
    (c : W ⟶ Y) (c' : X ⟶ Z)
    (hβ : βinv ≫ β = 𝟙 X) (hE : E ≫ Einv = 𝟙 Y)
    (h : β ≫ c' = c ≫ E) : βinv ≫ c = c' ≫ Einv := by
  calc
    βinv ≫ c = βinv ≫ (c ≫ E) ≫ Einv := by
      simp only [Category.assoc, hE, Category.comp_id]
    _ = βinv ≫ (β ≫ c') ≫ Einv := by rw [h]
    _ = c' ≫ Einv := by simp only [← Category.assoc, hβ, Category.id_comp]

/-- The compact-support exchange for the flipped self-product square intertwines the
actual chosen-compactification forget-supports maps, in both forward and inverse forms.
The ordinary exchange is `CoordinateTrace.exchange1`, the canonical derived adjunction
mate in the left-derived presentation of exact inverse image, as specified in
`definition-derived-base-change-map`. Its inverse is justified by torsion-ring proper base change.

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, first triangle, the common
pullback counits (auxiliary; not a blueprint node).

Proof in words:
1. Exact module inverse images and their right adjoints have the sheaf composition
normalization of situation-conventions and
lem-weil-pbc-inverse-image-composition-module-linear. Apply
lem-sfb-derived-composition-adjunction-normalization in the Grothendieck abelian module
sheaf categories (lem-weil-pbc-module-sheaves-grothendieck-abelian). Thus the K-injective
compositors of lem-weil-derived-direct-image-composition are conjugate to the canonical
pullback compositors. The ordinary exchange mates obey vertical pasting by
lem-weil-pbc-mate-pasting and lem-kun-derived-pullback-composition-monoidal.
2. Write the chosen compactification of f as (j,r), its base change as (j',r'), and
let a be the map between compactifying schemes. Put J=D(j_!), J'=D(j'_!), and let
b:F_a J -> J' F_v be inverse open exchange. Expanding exchangeFirst gives
beta^c=E_r(JK);R_r'(b_K), followed by the specified compactification comparison I.
The forget-supports maps are exactly the gamma maps of
lem-sf-proper-refinement-forget-supports.
3. Transpose the open forget-supports square under F_j' adjoint to R_j'. The unit-mate
identity lem-asd-open-base-change-unit-mate identifies the transpose of b;t_j' with
that of F_a(t_j);E_j. Indeed, t_j is the adjunct of the inverse open unit; naturality
of the pullback square and the counit give the same inverse-unit composite on both
sides. The adjunction hom bijection (def-weil-pbc-adjunction-mate) gives equality.
4. Substitute that equality in beta^c;gamma_c'. Naturality of E_r moves t_j past E_r;
vertical mate pasting then identifies E_r;R_r'(E_j);kappa_r',j' with
F_f(kappa_r,j);E_f. Consequently beta^c;gamma_c'=F_f(gamma_c);E_f.
5. Apply lem-sf-proper-refinement-forget-supports to the actual common refinement:
I;gamma_d=gamma_c'. The first equality follows. The projection is proper by
lem-weil-pbc-proper-base-change, so both proper comparisons apply.
6. A finite ring is additive torsion. By lem-kun-proper-base-change-torsion-ring,
E_f is invertible on every unbounded K. Precompose the first equation by beta_f inverse
and postcompose by E_f inverse to obtain the second equation. Conversely cancel those
isomorphisms. No trace, boundedness or condition on the base is used. -/
theorem proper_self_exchange_forget_supports
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (K : DerivedCategoryModule A X) :
    ((SfDiagonalKernel.exchangeFirst A f).hom.app K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (pullback.fst f f)).hom.app
            ((ordinaryFinitePullback A (pullback.snd f f)).obj K) =
      (ordinaryFinitePullback A f).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) f).hom.app K) ≫
        (CoordinateTrace.exchange1 A f K).hom) ∧
    ((SfDiagonalKernel.exchangeFirst A f).inv.app K ≫
        (ordinaryFinitePullback A f).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) f).hom.app K) =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (pullback.fst f f)).hom.app
            ((ordinaryFinitePullback A (pullback.snd f f)).obj K) ≫
        (CoordinateTrace.exchange1 A f K).inv) := by
  have h := proper_exchange A (IsPullback.of_hasPullback f f).flip K
  change (SfDiagonalKernel.exchangeFirst A f).hom.app K ≫ _ =
    _ ≫ (CoordinateTrace.exchange1 A f K).hom at h
  refine ⟨h, ?_⟩
  exact inverse_exchange
    ((SfDiagonalKernel.exchangeFirst A f).hom.app K)
    ((SfDiagonalKernel.exchangeFirst A f).inv.app K)
    (CoordinateTrace.exchange1 A f K).hom (CoordinateTrace.exchange1 A f K).inv _ _
    ((SfDiagonalKernel.exchangeFirst A f).inv_hom_id_app K)
    (CoordinateTrace.exchange1 A f K).hom_inv_id h

end AlgebraicGeometry.Etale
