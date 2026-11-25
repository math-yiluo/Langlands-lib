/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp

/-! # The formal mate step for the projective-line Chern map

(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor ChangeOfRings

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000]
  DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace

private lemma mate_ofNatIsoLeft
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (α : TwoSquare G L₁' L₂' H) :
    (mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α) =
      (mateEquiv adj₁ adj₂ ((α.whiskerRight e₂.hom).whiskerLeft e₁.inv)) := by
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Category.assoc, ← Functor.map_comp]

private lemma mate_whiskerTop
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : C ⥤ E} {H : D ⥤ F}
    (α : TwoSquare G' L₁ L₂ H) (γ : G ⟶ G') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerTop γ)).app K =
      γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_whiskerBottom
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : C ⥤ E} {H H' : D ⥤ F}
    (α : TwoSquare G L₁ L₂ H) (δ : H ⟶ H') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom δ)).app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, δ.naturality]

private lemma exact_exchange_transport
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) :
    Functor.whiskerLeft (rightDerivedLowerStar (ModuleCat.{u + 1} A) f)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
      derivedBaseChangeMap (ModuleCat.{u + 1} A) sq ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g').hom _ =
      exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq := by
  let B := ModuleCat.{u + 1} A
  let α := TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq).hom
  have hs :
      ((((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
        (leftDerivedUpperStarIsoMapDerivedCategory B g').inv).whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory B f').hom).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory B f).inv) =
      TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso B sq).hom := by
    ext M
    simp only [α, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.mk]
    simp only [derivedSquareUpperStarIso, leftDerivedUpperStarComp,
      exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.inv_hom_id_app_assoc]
    rw [← (upperStar B g').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  have hm := mate_ofNatIsoLeft
    (derivedUpperStarLowerStarAdjunction B f) (derivedUpperStarLowerStarAdjunction B f')
    (leftDerivedUpperStarIsoMapDerivedCategory B f)
    (leftDerivedUpperStarIsoMapDerivedCategory B f')
    ((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
      (leftDerivedUpperStarIsoMapDerivedCategory B g').inv)
  rw [← mapDerivedUpperStarLowerStarAdjunction_eq,
    ← mapDerivedUpperStarLowerStarAdjunction_eq, hs] at hm
  change _ = derivedBaseChangeMap B sq at hm
  rw [← hm]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [mate_whiskerBottom, mate_whiskerTop]
  change _ = (mateEquiv (mapDerivedUpperStarLowerStarAdjunction B f)
    (mapDerivedUpperStarLowerStarAdjunction B f') α).app K
  dsimp only [B, rightDerivedLowerStar, Functor.comp_obj]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma line_projective_exchange (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (g : S' ⟶ S) (M : DerivedCategoryModule A (ProjectiveLine S)) :
    ordinaryFiniteP1Exchange A g M =
      (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq).app M := by
  have h := NatTrans.congr_app (exact_exchange_transport A
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  rw [ordinaryFiniteP1Exchange, ← h]
  dsimp only [ordinaryFinitePushforward, rightDerivedLowerStar]
  simp [Category.assoc, ← Functor.map_comp]

private theorem adjunct_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    (θ : TwoSquare G L L' H) {A : C} {K : D} (z : L.obj A ⟶ K) :
    G.map (adj.homEquiv A K z) ≫ (mateEquiv adj adj' θ).app K =
      adj'.homEquiv (G.obj A) (H.obj K) (θ.app A ≫ H.map z) := by
  rw [adj.homEquiv_unit, G.map_comp, Category.assoc]
  have hn := (mateEquiv adj adj' θ).naturality z
  simp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc, unit_mateEquiv, Category.assoc, ← R'.map_comp,
    adj'.homEquiv_unit]
  rfl

private lemma adjunct_mate_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    (θ : TwoSquare G L L' H) {P : C} {Q K : D} {P' : E} {Q' K' : F}
    (a : L.obj P ⟶ Q) (b : G.obj P ⟶ P') (a' : L'.obj P' ⟶ Q')
    (v : H.obj Q ⟶ Q') (c : Q ⟶ K) (c' : Q' ⟶ K') (d : H.obj K ⟶ K')
    (hs : θ.app P ≫ H.map a ≫ v = L'.map b ≫ a')
    (hc : H.map c ≫ d = v ≫ c') :
    G.map (adj.homEquiv _ _ (a ≫ c)) ≫ (mateEquiv adj adj' θ).app K ≫
      R'.map d = b ≫ adj'.homEquiv _ _ (a' ≫ c') := by
  rw [reassoc_of% adjunct_mate adj adj' G H θ (a ≫ c)]
  rw [← adj'.homEquiv_naturality_right, ← adj'.homEquiv_naturality_left]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, reassoc_of% hs]

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors

private lemma comparison_square
    {C : Type*} [Category C] {P U V Q R T : C}
    (α : P ≅ U) (γ : P ≅ V)
    (a : U ⟶ Q) (b : Q ⟶ T) (c : V ⟶ R) (d : R ⟶ T) (z : P ⟶ T)
    (ha : a ≫ b = α.inv ≫ z) (hc : c ≫ d = γ.inv ≫ z) :
    (γ.inv ≫ α.hom) ≫ a ≫ b = c ≫ d := by
  rw [Category.assoc, ha, Iso.hom_inv_id_assoc, ← hc]

attribute [local irreducible] ordinaryFiniteUnitPullback

private lemma unit_comparison_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) (k : X ⟶ Z) (hk : k = g ≫ f) :
    (ordinaryFinitePullback A g).map (ordinaryFiniteUnitPullback A f).hom ≫
        (ordinaryFiniteUnitPullback A g).hom =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g f k hk).inv.app
        (ordinaryFiniteUnit A Z) ≫ (ordinaryFiniteUnitPullback A k).hom := by
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g f k hk).hom.app
    (ordinaryFiniteUnit A Z))).1
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
    ordinaryFiniteUnitPullback_comp A g f k hk

private lemma unit_comparison_square (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
        (ordinaryFiniteUnit A Y) ≫
      (ordinaryFinitePullback A g').map (ordinaryFiniteUnitPullback A f).hom ≫
      (ordinaryFiniteUnitPullback A g').hom =
    (ordinaryFinitePullback A f').map (ordinaryFiniteUnitPullback A g).hom ≫
      (ordinaryFiniteUnitPullback A f').hom := by
  exact comparison_square
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g' f).app _)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f' g (g' ≫ f) sq.w).app _)
    _ _ _ _ _ (unit_comparison_comp A g' f (g' ≫ f) rfl)
    (unit_comparison_comp A f' g (g' ≫ f) sq.w)

private lemma native_adjunct_square
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    {K : DerivedCategoryModule A X} {K' : DerivedCategoryModule A X'}
    (c : ordinaryFiniteUnit A X ⟶ K) (c' : ordinaryFiniteUnit A X' ⟶ K')
    (d : (ordinaryFinitePullback A g').obj K ⟶ K')
    (hc : (ordinaryFinitePullback A g').map c ≫ d =
      (ordinaryFiniteUnitPullback A g').hom ≫ c') :
    (ordinaryFinitePullback A g).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
        ((ordinaryFiniteUnitPullback A f).hom ≫ c)) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K ≫
        (ordinaryFinitePushforward A f').map d =
    (ordinaryFiniteUnitPullback A g).hom ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f').homEquiv _ _
        ((ordinaryFiniteUnitPullback A f').hom ≫ c') := by
  exact adjunct_mate_square
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f')
    (ordinaryFinitePullback A g) (ordinaryFinitePullback A g')
    (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom)
    (P := ordinaryFiniteUnit A Y) (P' := ordinaryFiniteUnit A Y')
    (ordinaryFiniteUnitPullback A f).hom (ordinaryFiniteUnitPullback A g).hom
    (ordinaryFiniteUnitPullback A f').hom (ordinaryFiniteUnitPullback A g').hom
    c c' d (unit_comparison_square A sq) hc

set_option linter.unusedVariables false in
/-- The Chern-map square transposes to the direct-image adjunct square.
Source: the mate-unit and mate-counit identities in
`lem-sp-finite-p1-chern-adjunct-base-change`, proof step 3.
(auxiliary; not a blueprint node)

Expand `ordinaryFiniteP1ChernPushforward` as the inverse-image/direct-image
adjunct, use the defining mate formula for `ordinaryFiniteP1Exchange`, and
cancel the adjunction correspondence.  The unit and counit triangle identities
leave exactly the displayed direct-image composite. -/
theorem ordinaryFiniteP1_chern_adjunct_of_map_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (c' : ordinaryFiniteUnit A (ProjectiveLine S') ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧)
    (hc : (ordinaryFinitePullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)).map c ≫
        (ordinaryFiniteShiftedLinePullback A N hA t
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
          ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
            hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
      (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)).hom ≫ c') :
    (ordinaryFinitePullback A f).map (ordinaryFiniteP1ChernPushforward A N hA S c) ≫
        ordinaryFiniteP1Exchange A f
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
              hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
      (ordinaryFiniteUnitPullback A f).hom ≫
        ordinaryFiniteP1ChernPushforward A N hA S' c' := by
  unfold ordinaryFiniteP1ChernPushforward
  rw [line_projective_exchange]
  exact native_adjunct_square A
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f).toCommSq c c' _ hc

end AlgebraicGeometry.Etale
