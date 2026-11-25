/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.SfP1ChartMapComposition
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar

/-! # Exchange before the projective-line trace

The chart comparison factors through exchange for the self-product square.
This is an equation before applying a trace, independent of any splitting family.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

/- The exact/left-derived mate calculation follows the proved private helpers of
AffineTraceLineOpenCounitBaseChange. -/
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

private lemma chart_square
    (A : Type (u + 1)) [CommRing A]
    {E W X Z Y : Scheme.{u}} {v : W ⟶ Z} {p : W ⟶ X}
    {f : Z ⟶ Y} {g : X ⟶ Y} (sq : CommSq v p f g)
    (e : E ⟶ W) (r : E ⟶ X) (k : E ⟶ Z)
    (hp : r = e ≫ p) (hv : k = e ≫ v) (sq' : CommSq k r f g)
    (K : DerivedCategoryModule A Y) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e p r hp).hom.app
        ((ordinaryFinitePullback A g).obj K) ≫
      (ordinaryFinitePullback A e).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app K) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e v k hv).inv.app
        ((ordinaryFinitePullback A f).obj K) =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq').hom.app K := by
  dsimp only [ordinaryFinitePullback]
  let B := ModuleCat.{u + 1} A
  have h₁ := leftDerivedUpperStarComp_assoc'_app B e p g r (v ≫ f) (k ≫ f)
    hp sq.w sq'.w K
  have h₂ := leftDerivedUpperStarComp_assoc'_app B e v f k (v ≫ f) (k ≫ f)
    hv rfl rfl K
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  dsimp only [B] at h₁ h₂
  rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r g (k ≫ f) sq'.w).hom.app K)]
  rw [← reassoc_of% h₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% h₂, Iso.hom_inv_id_app, Category.comp_id, Iso.hom_inv_id_app_assoc]

private lemma chart_exchange_derived
    (A : Type (u + 1)) [CommRing A]
    {E W X Z Y : Scheme.{u}} {v : W ⟶ Z} {p : W ⟶ X}
    {f : Z ⟶ Y} {g : X ⟶ Y} (sq : CommSq v p f g)
    (e : E ⟶ W) (r : E ⟶ X) (k : E ⟶ Z)
    (hp : r = e ≫ p) (hv : k = e ≫ v) (sq' : CommSq k r f g)
    (M : DerivedCategoryModule A Z) :
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app M ≫
      (ordinaryFinitePushforward A p).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app
          ((ordinaryFinitePullback A v).obj M)) ≫
      (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) e p r hp).app
        ((ordinaryFinitePullback A e).obj ((ordinaryFinitePullback A v).obj M)) ≫
      (ordinaryFinitePushforward A r).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e v k hv).inv.app M) =
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq').app M := by
  let B := ModuleCat.{u + 1} A
  apply ((derivedUpperStarLowerStarAdjunction B r).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [Adjunction.counit_naturality,
    map_rightDerivedLowerStarCompHom_app_counit_assoc]
  rw [← Functor.map_comp_assoc]
  have hn := (leftDerivedUpperStarComp B e p r hp).hom.naturality
    ((derivedBaseChangeMap B sq).app M ≫
      (ordinaryFinitePushforward A p).map
        ((derivedUpperStarLowerStarAdjunction B e).unit.app
          ((ordinaryFinitePullback A v).obj M)))
  dsimp only [B, ordinaryFinitePullback, ordinaryFinitePushforward] at hn ⊢
  rw [reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc]
  have hc := (derivedUpperStarLowerStarAdjunction B p).counit.naturality
    ((derivedUpperStarLowerStarAdjunction B e).unit.app
      ((ordinaryFinitePullback A v).obj M))
  dsimp only [B, ordinaryFinitePullback, Functor.comp_map, Functor.id_map,
    Functor.comp_obj, Functor.id_obj] at hc
  rw [← (upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor.map_comp_assoc
    ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
      ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app
          ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj M)))) _, hc]
  rw [Functor.map_comp_assoc, Adjunction.left_triangle_components_assoc]
  rw [← Functor.map_comp_assoc, derivedUpperStar_map_derivedBaseChangeMap_app_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hvn := (leftDerivedUpperStarComp B e v k hv).inv.naturality
    ((derivedUpperStarLowerStarAdjunction B f).counit.app M)
  dsimp only [B, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hvn
  rw [hvn]
  have hs := chart_square A sq e r k hp hv sq'
    ((ordinaryFinitePushforward A f).obj M)
  dsimp only [ordinaryFinitePullback, ordinaryFinitePushforward] at hs
  rw [reassoc_of% hs]
  exact (derivedUpperStar_map_derivedBaseChangeMap_app_counit B sq' M).symm

/- The degree-zero and shift calculations adapt the proved private helpers of
FiniteP1TwistedUnitBaseChange. -/
section LineComparisons

attribute [local instance 2000] Abelian.toPreadditive

private theorem pullback_additive (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) f).Additive := by
  infer_instance

private theorem pullback_limits (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (upperStar (ModuleCat.{u + 1} A) f) := by
  infer_instance

private theorem pullback_colimits (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (upperStar (ModuleCat.{u + 1} A) f) := by
  infer_instance

attribute [local instance] pullback_additive pullback_limits pullback_colimits

attribute [local irreducible] upperStar lowerStar Scheme.finiteEtaleTateLine
  DerivedCategory.singleFunctors
  ordinaryFiniteSinglePullbackIso
  ordinaryFiniteSingleExactPullbackIso

-- The cached functor now stores ordinaryFiniteDegreeZero as its object field.
-- Expose this projection locally while retaining the cached comparison isomorphisms.
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

private theorem line_comp (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsUnit (N : Γ(Z, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    (t.line fg hZ).hom =
      (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) f).map (t.line g hZ).hom ≫
          (t.line f hY).hom := by
  subst fg
  by_cases hN : N = 0
  · subst N
    have hsub : Subsingleton Γ(Z, ⊤) :=
      subsingleton_of_zero_eq_one (isUnit_zero_iff.mp (by simpa using hZ))
    let : IsEmpty Z := Scheme.isEmpty_of_subsingleton_Γ hsub
    let : IsEmpty X := ⟨fun x ↦ isEmptyElim ((f ≫ g).base x)⟩
    exact (Scheme.Etale.isZero_sheaf_of_isEmpty
      (X.finiteEtaleTateLine 0 A hA)).eq_of_tgt _ _
  let d := Scheme.finiteEtaleTwistPullbackData A N (Nat.pos_of_ne_zero hN) hA
  let t' : OrdinaryFiniteTwistTransport A N hA := {
    roots := d.r
    line := fun v hT ↦ d.c v hT
      ((map_natCast v.appTop.hom N) ▸ hT.map v.appTop.hom) 1
    roots_normalization := d.laws.2.1
    line_normalization := fun v hT ↦ d.laws.2.2.1 v hT _ }
  have ht := ordinaryFiniteTwistTransport_unique A N hA t t'
  subst t
  exact congrArg Iso.hom (d.laws.2.2.2.2.2.2.2.1 g f hZ hY
    ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) 1)

/-- Cache the unshifted comparison before specializing the categories. -/
@[irreducible] private def singleComparisonHom
    {C D C₀ D₀ : Type*} [Category C] [Category D] [Category C₀] [Category D₀]
    (F : C ⥤ D) (single : C₀ ⥤ C) (single' : D₀ ⥤ D) (pull : C₀ ⥤ D₀)
    (s : single ⋙ F ≅ pull ⋙ single') (K : C₀) (M : D₀) (a : pull.obj K ≅ M) :
    F.obj (single.obj K) ⟶ single'.obj M :=
  s.hom.app K ≫ single'.map a.hom

/-- Cache shifting a morphism before specializing the categories. -/
@[irreducible] private def shiftedHom
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {K : C} {M : D} (a : F.obj K ⟶ M) (n : ℤ) :
    F.obj (K⟦n⟧) ⟶ M⟦n⟧ :=
  (F.commShiftIso n).hom.app K ≫ a⟦n⟧'

/-- The exact degree-zero comparison through the cached embeddings. -/
@[irreducible] private def exactLine₀ (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) f).obj K ≅ M) :=
  singleComparisonHom (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (ordinaryFiniteSingleFunctor A Y) (ordinaryFiniteSingleFunctor A X)
    (upperStar (ModuleCat.{u + 1} A) f) (ordinaryFiniteSingleExactPullbackIso A f) K M a

/-- Shift the exact comparison while retaining the ordinary object interface. -/
@[irreducible] private def exactLine (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) f).obj K ≅ M) :=
  shiftedHom (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (exactLine₀ A f a) (2 : ℤ)

private theorem compared_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ G) [NatTrans.CommShift e.hom ℤ] {K : C} {M : D}
    (a : G.obj K ⟶ M) (n : ℤ) :
    (F.commShiftIso n).hom.app K ≫ (e.hom.app K ≫ a)⟦n⟧' =
      e.hom.app (K⟦n⟧) ≫ shiftedHom G a n := by
  simp only [shiftedHom, Functor.map_comp]
  rw [NatTrans.shift_app_comm_assoc]

private theorem compared_shift_iso
    {C D C₀ D₀ : Type*} [Category C] [Category D] [Category C₀] [Category D₀]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ G) [NatTrans.CommShift e.hom ℤ]
    (single : C₀ ⥤ C) (single' : D₀ ⥤ D) (pull : C₀ ⥤ D₀)
    (s : single ⋙ G ≅ pull ⋙ single') (K : C₀) (M : D₀)
    (a : pull.obj K ≅ M) (n : ℤ) :
    ((F.commShiftIso n).app (single.obj K) ≪≫
      (shiftFunctor D n).mapIso
        ((Functor.isoWhiskerLeft single e ≪≫ s).app K ≪≫ single'.mapIso a)).hom =
      e.hom.app ((single.obj K)⟦n⟧) ≫
        shiftedHom G (singleComparisonHom G single single' pull s K M a) n := by
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app]
  simp only [Category.assoc]
  unfold singleComparisonHom
  exact compared_shift e _ n

private theorem singleComparison_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFiniteSinglePullbackIso A f =
      Functor.isoWhiskerLeft (ordinaryFiniteSingleFunctor A Y)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
      ordinaryFiniteSingleExactPullbackIso A f := by
  unfold ordinaryFiniteSinglePullbackIso
  rfl

private theorem shiftedSingle_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) f).obj K ≅ M) :
    letI : (ordinaryFinitePullback A f).CommShift ℤ :=
      commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
    (((ordinaryFinitePullback A f).commShiftIso (2 : ℤ)).app
        (ordinaryFiniteDegreeZero A Y K) ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso
        ((ordinaryFiniteSinglePullbackIso A f).app K ≪≫
          (ordinaryFiniteSingleFunctor A X).mapIso a)).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
        ((ordinaryFiniteDegreeZero A Y K)⟦(2 : ℤ)⟧) ≫ exactLine A f a := by
  let : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  have : NatTrans.CommShift
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm ℤ
  have : NatTrans.CommShift
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom ℤ :=
    NatTrans.CommShift.of_iso_inv
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm ℤ
  unfold exactLine exactLine₀
  rw [singleComparison_eq]
  exact compared_shift_iso
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (ordinaryFiniteSingleFunctor A Y) (ordinaryFiniteSingleFunctor A X)
    (upperStar (ModuleCat.{u + 1} A) f) (ordinaryFiniteSingleExactPullbackIso A f)
    K M a (2 : ℤ)

private theorem shiftedLine_eq (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app _ ≫
        exactLine A f (t.line f hY) := by
  unfold ordinaryFiniteShiftedLinePullback
  exact shiftedSingle_eq A f (t.line f hY)

private theorem raw_single_coherence
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : H ≅ F ⋙ G) :
    Functor.whiskerLeft (DerivedCategory.singleFunctor C 0)
        (Functor.mapDerivedCategoryNatIso e ≪≫
          (Functor.mapDerivedCategoryCompIso F G).symm).hom ≫
      Functor.whiskerRight (F.mapDerivedCategorySingleFunctor 0).hom G.mapDerivedCategory ≫
      Functor.whiskerLeft F (G.mapDerivedCategorySingleFunctor 0).hom =
      (H.mapDerivedCategorySingleFunctor 0).hom ≫
        Functor.whiskerRight e.hom (DerivedCategory.singleFunctor E 0) := by
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Category.assoc]
  exact Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor F G H e K

private theorem singleComparisonHom_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (S₀ : C₀ ⥤ D₀) (S₁ : C₁ ⥤ D₁) (S₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (DF : D₀ ⥤ D₁) (DG : D₁ ⥤ D₂) (DH : D₀ ⥤ D₂)
    (e : H ≅ F ⋙ G) (de : DH ≅ DF ⋙ DG)
    (sF : S₀ ⋙ DF ≅ F ⋙ S₁) (sG : S₁ ⋙ DG ≅ G ⋙ S₂)
    (sH : S₀ ⋙ DH ≅ H ⋙ S₂)
    (hc : Functor.whiskerLeft S₀ de.hom ≫
        Functor.whiskerRight sF.hom DG ≫ Functor.whiskerLeft F sG.hom =
      sH.hom ≫ Functor.whiskerRight e.hom S₂)
    {K : C₀} {L : C₁} {M : C₂}
    (a : F.obj K ≅ L) (b : G.obj L ≅ M) (d : H.obj K ≅ M)
    (h : e.hom.app K ≫ G.map a.hom ≫ b.hom = d.hom) :
    de.hom.app (S₀.obj K) ≫
        DG.map (singleComparisonHom DF S₀ S₁ F sF K L a) ≫
          singleComparisonHom DG S₁ S₂ G sG L M b =
      singleComparisonHom DH S₀ S₂ H sH K M d := by
  unfold singleComparisonHom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := sG.hom.naturality a.hom
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hc' := congr_app hc K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc'
  rw [reassoc_of% hc']
  rw [← Functor.map_comp, ← Functor.map_comp, h]

private theorem raw_comparison_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : H ≅ F ⋙ G)
    {K : C} {L : D} {M : E} (a : F.obj K ≅ L) (b : G.obj L ≅ M)
    (d : H.obj K ≅ M) (h : e.hom.app K ≫ G.map a.hom ≫ b.hom = d.hom) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
          ((DerivedCategory.singleFunctor C 0).obj K) ≫
      G.mapDerivedCategory.map
        (singleComparisonHom F.mapDerivedCategory (DerivedCategory.singleFunctor C 0)
          (DerivedCategory.singleFunctor D 0) F (F.mapDerivedCategorySingleFunctor 0) K L a) ≫
      singleComparisonHom G.mapDerivedCategory (DerivedCategory.singleFunctor D 0)
        (DerivedCategory.singleFunctor E 0) G (G.mapDerivedCategorySingleFunctor 0) L M b =
      singleComparisonHom H.mapDerivedCategory (DerivedCategory.singleFunctor C 0)
        (DerivedCategory.singleFunctor E 0) H (H.mapDerivedCategorySingleFunctor 0) K M d := by
  exact singleComparisonHom_comp
    (DerivedCategory.singleFunctor C 0) (DerivedCategory.singleFunctor D 0)
    (DerivedCategory.singleFunctor E 0) F G H _ _ _ e _
    (F.mapDerivedCategorySingleFunctor 0) (G.mapDerivedCategorySingleFunctor 0)
    (H.mapDerivedCategorySingleFunctor 0) (raw_single_coherence F G H e) a b d h

private theorem exactLine₀_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    {K : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) g).obj K ≅ L)
    (b : (upperStar (ModuleCat.{u + 1} A) f).obj L ≅ M)
    (d : (upperStar (ModuleCat.{u + 1} A) fg).obj K ≅ M)
    (h : (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app K ≫
      (upperStar (ModuleCat.{u + 1} A) f).map a.hom ≫ b.hom = d.hom) :
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app (ordinaryFiniteDegreeZero A Z K) ≫
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
          (exactLine₀ A g a) ≫ exactLine₀ A f b = exactLine₀ A fg d := by
  unfold exactLine₀ ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor
    ordinaryFiniteSingleExactPullbackIso
  exact raw_comparison_comp
    (upperStar (ModuleCat.{u + 1} A) g) (upperStar (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} A) fg)
    (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg) a b d h

private theorem shift_composite
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (e : H ≅ F ⋙ G) [NatTrans.CommShift e.hom ℤ]
    {K : C} {L : D} {M : E} (a : F.obj K ⟶ L) (b : G.obj L ⟶ M)
    (d : H.obj K ⟶ M) (h : e.hom.app K ≫ G.map a ≫ b = d) (n : ℤ) :
    e.hom.app (K⟦n⟧) ≫ G.map ((F.commShiftIso n).hom.app K ≫ a⟦n⟧') ≫
        (G.commShiftIso n).hom.app L ≫ b⟦n⟧' =
      (H.commShiftIso n).hom.app K ≫ d⟦n⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [G.commShiftIso_hom_naturality_assoc]
  have he := NatTrans.shift_app_comm e.hom n K
  simp only [Functor.commShiftIso_comp_hom_app] at he
  rw [← reassoc_of% he]
  simp only [← Functor.map_comp, h]

private theorem compared_composite
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : C ⥤ E}
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H') (c : H' ≅ F' ⋙ G')
    {K : C} {B : D} {V : E} (a : F'.obj K ⟶ B) (b : G'.obj B ⟶ V)
    (d : H'.obj K ⟶ V) (hc : c.hom.app K ≫ G'.map a ≫ b = d) :
    (eH ≪≫ c ≪≫ Functor.isoWhiskerRight eF.symm G' ≪≫
        Functor.isoWhiskerLeft F eG.symm).hom.app K ≫
      G.map (eF.hom.app K ≫ a) ≫ eG.hom.app B ≫ b = eH.hom.app K ≫ d := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc]
  rw [← eG.inv.naturality_assoc]
  rw [← G'.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hc]

/-- Use the cached object field without unfolding the derived embedding. -/
private theorem singleFunctor_obj (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ordinaryFiniteSingleFunctor A T).obj K = ordinaryFiniteDegreeZero A T K := rfl

private theorem shiftedLine_comp
    (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsUnit (N : Γ(Z, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app
        ((ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePullback A f).map (ordinaryFiniteShiftedLinePullback A N hA t g hZ).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom =
      (ordinaryFiniteShiftedLinePullback A N hA t fg hZ).hom := by
  let c := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  have hc₀ := exactLine₀_comp A f g fg hfg
    (t.line g hZ) (t.line f hY) (t.line fg hZ)
    (line_comp A N hA t f g hZ hY fg hfg).symm
  have : NatTrans.CommShift c.hom ℤ := by
    dsimp only [c, Iso.trans_hom]
    infer_instance
  have hc := shift_composite
    (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) fg).mapDerivedCategory c
    (exactLine₀ A g (t.line g hZ)) (exactLine₀ A f (t.line f hY))
    (exactLine₀ A fg (t.line fg hZ)) hc₀ (2 : ℤ)
  have hc' : c.hom.app ((ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧) ≫
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
      (exactLine A g (t.line g hZ)) ≫ exactLine A f (t.line f hY) =
    exactLine A fg (t.line fg hZ) := by
    simpa only [exactLine, shiftedHom, ordinaryFiniteLine, singleFunctor_obj,
      Category.assoc] using hc
  have h := compared_composite
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) fg) c
    (exactLine A g (t.line g hZ)) (exactLine A f (t.line f hY))
    (exactLine A fg (t.line fg hZ)) hc'
  simp only [shiftedLine_eq]
  dsimp only [ordinaryFinitePullback, ordinaryFiniteLine, ordinaryFiniteSingleFunctor] at h ⊢
  simpa (config := { dsimp := false }) only [ordinaryFinitePullback, ordinaryFiniteLine,
    singleFunctor_obj,
    shiftedLine_eq, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, c, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc] using h

end LineComparisons

attribute [local irreducible] upperStar lowerStar Scheme.finiteEtaleTateLine
  ordinaryFiniteSingleFunctor DerivedCategory.singleFunctors

private lemma unit_comparison_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (P : C ⥤ E) (Q : D ⥤ E)
    (c : R ⋙ P ⟶ Q) {K B : C} {V : D} (a : K ≅ B) (b : L.obj B ⟶ V) :
    P.map a.inv ≫ P.map (adj.unit.app K) ≫ c.app (L.obj K) ≫
        Q.map (L.map a.hom ≫ b) =
      P.map (adj.unit.app B) ≫ c.app (L.obj B) ≫ Q.map b := by
  have hn := adj.unit.naturality a.inv
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hc := c.naturality (L.map a.inv)
  dsimp only [Functor.comp_map] at hc
  rw [← P.map_comp_assoc, hn, P.map_comp_assoc, reassoc_of% hc]
  rw [← Q.map_comp, ← L.map_comp_assoc, Iso.inv_hom_id, L.map_id, Category.id_comp]

private lemma exchange_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (P : C ⥤ E) (Q : D ⥤ E)
    (c : R ⋙ P ⟶ Q) {K B : C} {U V : D} {T : E}
    (a : K ≅ B) (b : L.obj B ⟶ V) (β : T ≅ P.obj K)
    (χ : T ⟶ Q.obj U) (d : L.obj K ⟶ U) (l : U ⟶ V)
    (hβ : β.hom ≫ P.map (adj.unit.app K) ≫ c.app (L.obj K) ≫ Q.map d = χ)
    (hl : d ≫ l = L.map a.hom ≫ b) :
    P.map a.inv ≫ β.inv ≫ χ ≫ Q.map l =
      P.map (adj.unit.app B) ≫ c.app (L.obj B) ≫ Q.map b := by
  rw [← hβ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Q.map_comp, hl]
  exact unit_comparison_transport adj P Q c a b

/-- The opposite projection is the horizontal side of the self-product square. -/
theorem projectiveProjectionSquare (S : Scheme.{u}) (a : Bool) :
    IsPullback (projectiveLineDiagonalProjection S (!a))
      (projectiveLineDiagonalProjection S a) (ProjectiveLine S ↘ S)
      (ProjectiveLine S ↘ S) := by
  cases a
  · exact (IsPullback.of_hasPullback (ProjectiveLine S ↘ S)
      (ProjectiveLine S ↘ S)).flip
  · exact IsPullback.of_hasPullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)

private lemma chart_opposite (S : Scheme.{u}) (a : Bool) :
    (projectiveLineDiagonalChart S a).val.hom ≫ projectiveLineDiagonalProjection S (!a) =
      ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S) := by
  cases a
  · exact (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2))
      (ProjectiveLine S ↘ S)).flip.isoPullback_hom_snd
  · exact (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2))
      (ProjectiveLine S ↘ S)).isoPullback_hom_fst

/-- The ordinary exchange from a product projection, with its twist endpoint corrected.
It is defined before, and independently of, any trace or decomposition.
Source: blueprint thm-amb-p1-adjunction.proof.md, the proper base-change identification
for either projection (auxiliary; not a blueprint node). -/
@[irreducible]
def projectionExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      (ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteP1SplittingTarget A N hA S) :=
  (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
      (ordinaryFiniteShiftedLinePullback A N hA t
        (projectiveLineDiagonalProjection S (!a))
        (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv ≫
    (properExchange A (projectiveProjectionSquare S a)).inv.app
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

private theorem chartExchange_aux
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    projectionExchange A N hA t S hS a ≫
        ordinaryFiniteP1Exchange A (ProjectiveLine S ↘ S)
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A
          (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S))
            (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).hom =
      ordinaryFiniteP1DiagonalChartMap A N hA t S hS a := by
  let e := (projectiveLineDiagonalChart S a).val.hom
  let p := projectiveLineDiagonalProjection S a
  let v := projectiveLineDiagonalProjection S (!a)
  let q := ProjectiveLine S ↘ S
  let r := ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S
  let k := ProjectiveSpace.map (ULift.{u} (Fin 2)) q
  let M := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  let hP := finiteP1_unitOnPullback N q hS
  let hW := finiteP1_unitOnPullback N v hP
  have hp : r = e ≫ p := (projectiveLineDiagonalChart S a).property.symm
  have hv : k = e ≫ v := (chart_opposite S a).symm
  let sq := projectiveProjectionSquare S a
  let sq' := ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) q
  have hβ := chart_exchange_derived A sq.toCommSq e r k hp hv sq'.toCommSq M
  have hβ' :
      (properExchange A sq).hom.app M ≫
        (ordinaryFinitePushforward A p).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app
            ((ordinaryFinitePullback A v).obj M)) ≫
        (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) e p r hp).app
          ((ordinaryFinitePullback A e).obj ((ordinaryFinitePullback A v).obj M)) ≫
        (ordinaryFinitePushforward A r).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e v k hv).inv.app M) =
      ordinaryFiniteP1Exchange A q M := by
    simpa only [properExchange, asIso_hom, line_projective_exchange] using hβ
  have hl := shiftedLine_comp A N hA t e v hP hW k hv
  have hl' :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e v k hv).inv.app M ≫
          (ordinaryFiniteShiftedLinePullback A N hA t k hP).hom =
        (ordinaryFinitePullback A e).map
            (ordinaryFiniteShiftedLinePullback A N hA t v hP).hom ≫
          (ordinaryFiniteShiftedLinePullback A N hA t e hW).hom := by
    rw [← hl, Iso.inv_hom_id_app_assoc]
  have h := exchange_transport
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e)
    (ordinaryFinitePushforward A p) (ordinaryFinitePushforward A r)
    (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) e p r hp)
    (ordinaryFiniteShiftedLinePullback A N hA t v hP)
    (ordinaryFiniteShiftedLinePullback A N hA t e hW).hom
    ((properExchange A sq).app M) (ordinaryFiniteP1Exchange A q M)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e v k hv).inv.app M)
    (ordinaryFiniteShiftedLinePullback A N hA t k hP).hom hβ' hl'
  have hmap := chartMap_compHom A N hA t S hS a hW
  dsimp only [ordinaryFinitePullback] at hmap
  refine Eq.trans ?_ hmap.symm
  dsimp only [ordinaryFiniteP1DiagonalTarget] at h ⊢
  simpa only [projectionExchange, Iso.app_inv, Category.assoc] using h

/-- The chart pushforward is product exchange followed by projective-space exchange.
Neither side contains a trace, a Chern class, or a splitting family.

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the paragraph identifying each projection with
base change of q (auxiliary; not a blueprint node).

Proof: Let e be the canonical chart PP -> P times_S P, r:PP -> P and q:P -> S.
The equations e followed by the selected projection equals r, and e followed by
its opposite equals ProjectiveSpace.map q, are the two equations of isoPullback
(or its flipped square). Substitute the adjunction-mate formulas for both
exchanges. Precompose with the invertible product exchange to remove its inverse.
The two pullback square comparisons paste to the chart comparison. Substituting
the composite-adjunction counit and naturality moves the chart adjunction unit
next to its counit; the triangle identity cancels them. The remaining direct-image
composition and congruence factors are precisely those in the chart map.
For the twist factors, the root inclusions determine the root comparison uniquely
because the kernel inclusion is monic. The pure scalar generators determine the
coefficient comparison, so these comparisons commute with the same pasted square.
Deriving and then shifting preserves this equality. Finally transport between exact
termwise and left-derived inverse images using their canonical comparisons; both
adjunctions are the canonical derived adjunctions. This gives the displayed
factorization. The argument uses no trace, normalization of a trace, or diagonal
integral. It applies to both projections, to an empty base and to the zero ring. -/
theorem chartExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    projectionExchange A N hA t S hS a ≫
        ordinaryFiniteP1Exchange A (ProjectiveLine S ↘ S)
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A
          (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S))
            (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).hom =
      ordinaryFiniteP1DiagonalChartMap A N hA t S hS a := by
  exact chartExchange_aux A N hA t S hS a

end AlgebraicGeometry.Etale.SfP1Transport
