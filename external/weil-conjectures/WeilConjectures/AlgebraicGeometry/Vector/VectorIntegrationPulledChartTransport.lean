/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefix
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRestrictedChartCoefficientCore
import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceUnitCompactBaseChange
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence

/-! # Pulling a single frame chart along an arbitrary map

(blueprint: lem-pur-vector-integration-pulled-chart-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
attribute [local irreducible] affineLinearCoefficientDescent affineLinearBaseCoefficient
  leftDerivedUpperStarComp derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory sheafIsAbelian

/-- An inverse frame chart remains Cartesian after any pullback of its base.
Source: vector-bundle purity proof paragraph 2, restriction of a frame.
(blueprint: lem-pur-vector-integration-pulled-chart-transport). -/
theorem vectorIntegrationPulledChart_isPullback
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (W : Scheme.{u}) (k : W ⟶ V.toScheme) (j : W ⟶ S) (ha : j = k ≫ V.ι) :
    IsPullback (affineTraceMap k d ≫ vectorIntegrationChart S d F V e)
      (affineTraceProjection W d) (VectorBundleZeroSection.π S d F) j := by
  subst j
  exact (affineTraceMap_isPullback k d).paste_horiz
    (vectorIntegrationChart_isPullback S d F V e)

private lemma inverse_paste
    {C : Type*} [Category C] {P Q R S T : C}
    (a : P ≅ Q) (b : Q ≅ R) (c : R ≅ S) (d : S ≅ T) (e : P ≅ T)
    (h : a.hom ≫ b.hom ≫ c.hom ≫ d.hom = e.hom) :
    d.inv ≫ c.inv ≫ b.inv = e.inv ≫ a.hom := by
  have hi : a ≪≫ b ≪≫ c ≪≫ d = e := Iso.ext h
  have hh := congrArg Iso.inv hi
  simp only [Iso.trans_inv, Category.assoc] at hh
  calc
    _ = (d.inv ≫ c.inv ≫ b.inv ≫ a.inv) ≫ a.hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by rw [hh]

private lemma coefficient_composition
    {C D E B B' : Type*} [Category C] [Category D] [Category E]
    [Category B] [Category B']
    (G : C ⥤ D) (F : D ⥤ E) (J : C ⥤ E)
    (H : B ⥤ B') (R : D ⥤ B) (T : E ⥤ B')
    (c : J ≅ G ⋙ F) (s : R ⋙ H ≅ F ⋙ T) (L : C)
    {X X₁ X₂ Y : B} {Z W : B'} {K : D} {M : E}
    (a : Z ⟶ H.obj X) (i₁ : X ≅ X₁) (i₂ : X₁ ≅ X₂) (i₃ : X₂ ≅ R.obj (G.obj L))
    (bV : G.obj L ≅ K) (bF : F.obj K ≅ M) (bU : J.obj L ≅ M)
    (dV : Y ≅ R.obj K) (dU : W ≅ T.obj M) (z : Z ≅ T.obj (J.obj L))
    (ha : a ≫ H.map (i₁ ≪≫ i₂ ≪≫ i₃).hom ≫ s.hom.app (G.obj L) =
      z.hom ≫ T.map (c.hom.app L))
    (hb : c.hom.app L ≫ F.map bV.hom ≫ bF.hom = bU.hom) :
    a ≫ H.map (i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ R.mapIso bV ≪≫ dV.symm).hom ≫
        H.map dV.hom ≫ s.hom.app K ≫ T.map bF.hom ≫ dU.inv =
      (z ≪≫ T.mapIso bU ≪≫ dU.symm).hom := by
  have hn := s.hom.naturality bV.hom
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc] at ha
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% ha]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [hb]

private lemma named_compositor
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (r : X ⟶ Y) (v : Y ⟶ Z) (k : X ⟶ Z) (e : k = r ≫ v) :
    eqToIso (congrArg (ordinaryFinitePullback A) e) ≪≫
        leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v k e := by
  subst k
  simp only [eqToIso_refl, Iso.refl_trans]

private lemma square_iso_calculation
    {C D : Type*} [Category C] [Category D] {F G H K : C ⥤ D}
    (a : F ≅ K) (b : G ≅ H) (c : F ≅ H) (e : F = G)
    (h : eqToIso e ≪≫ b = c) :
    a.symm ≪≫ eqToIso e ≪≫ b = (c.symm ≪≫ a).symm := by
  rw [h, Iso.trans_symm, Iso.symm_symm_eq]

private lemma inverse_square_comparison
    (A : Type (u + 1)) [CommRing A] {X X' Y Y' : Scheme.{u}}
    (q : X' ⟶ X) (r : X' ⟶ Y') (p : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : CommSq q r p v) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).symm ≪≫
      eqToIso (congrArg (ordinaryFinitePullback A) sq.w) ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm := by
  delta derivedSquareUpperStarIso
  exact square_iso_calculation
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v (q ≫ p) sq.w)
    (congrArg (ordinaryFinitePullback A) sq.w)
    (named_compositor A r v (q ≫ p) sq.w)

private lemma component_composition
    {C D : Type*} [Category C] [Category D] {F G H K : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (c : H ≅ K) (s : F ≅ K)
    (h : a ≪≫ b ≪≫ c = s) (L : C) :
    (a.app L ≪≫ b.app L ≪≫ c.app L).hom = s.hom.app L := by
  exact congrArg (fun z ↦ z.hom.app L) h

private lemma mapped_middle
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (g h : X ⟶ Y) {Z W : D} (a : Z ⟶ F.obj X) (b : F.obj Y ⟶ W)
    {z : Z ⟶ W} (hg : g = h) (hh : a ≫ F.map h ≫ b = z) :
    a ≫ F.map g ≫ b = z := by
  rw [hg]
  exact hh

private lemma restricted_chart_geometry
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (W : Scheme.{u}) (k : W ⟶ V.toScheme) (j : W ⟶ S) (ha : j = k ≫ V.ι)
    (L : DerivedCategoryModule A S) :
    let q := vectorIntegrationChart S d F V e
    let a := affineTraceMap k d
    let r := affineTraceProjection W d
    let sq₁ := (vectorIntegrationChart_isPullback S d F V e).toCommSq
    let sq₂ := (affineTraceMap_isPullback k d).toCommSq
    let sq := (vectorIntegrationPulledChart_isPullback S d F V e W k j ha).toCommSq
    let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      k V.ι j ha
    let i₁ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q
      (VectorBundleZeroSection.π S d F)).symm.app L
    let i₂ := (eqToIso (congrArg (ordinaryFinitePullback A) sq₁.w)).app L
    let i₃ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (affineTraceProjection V.toScheme d) V.ι).app L
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a q
      (affineTraceMap k d ≫ vectorIntegrationChart S d F V e) rfl).hom.app
        ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj L) ≫
      (ordinaryFinitePullback A a).map (i₁ ≪≫ i₂ ≪≫ i₃).hom ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₂).inv.app
        ((ordinaryFinitePullback A V.ι).obj L) =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app L ≫
      (ordinaryFinitePullback A r).map (c.hom.app L) := by
  let q := vectorIntegrationChart S d F V e
  let a := affineTraceMap k d
  let r := affineTraceProjection W d
  let sq₁ := (vectorIntegrationChart_isPullback S d F V e).toCommSq
  let sq₂ := (affineTraceMap_isPullback k d).toCommSq
  let sq := (vectorIntegrationPulledChart_isPullback S d F V e W k j ha).toCommSq
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    k V.ι j ha
  have hp := derivedSquareUpperStarIso_paste (ModuleCat.{u + 1} A) sq₁ sq₂ sq
    rfl ha L
  have hinv' :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a q
        (affineTraceMap k d ≫ vectorIntegrationChart S d F V e) rfl).hom.app
          ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj L) ≫
        (ordinaryFinitePullback A a).map
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₁).inv.app L) ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₂).inv.app
          ((ordinaryFinitePullback A V.ι).obj L) =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app L ≫
        (ordinaryFinitePullback A r).map (c.hom.app L) := by
    have h := inverse_paste
      ((ordinaryFinitePullback A r).mapIso (c.app L))
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₂).app
        ((ordinaryFinitePullback A V.ι).obj L))
      ((ordinaryFinitePullback A a).mapIso
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₁).app L))
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a q
        (affineTraceMap k d ≫ vectorIntegrationChart S d F V e) rfl).symm.app
        ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj L))
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).app L) hp
    exact h
  let i₁ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q
    (VectorBundleZeroSection.π S d F)).symm.app L
  let i₂ := (eqToIso (congrArg (ordinaryFinitePullback A) sq₁.w)).app L
  let i₃ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (affineTraceProjection V.toScheme d) V.ι).app L
  have hg := component_composition
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q
      (VectorBundleZeroSection.π S d F)).symm
    (eqToIso (congrArg (ordinaryFinitePullback A) sq₁.w))
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (affineTraceProjection V.toScheme d) V.ι)
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₁).symm
    (inverse_square_comparison A q (affineTraceProjection V.toScheme d)
      (VectorBundleZeroSection.π S d F) V.ι sq₁) L
  exact mapped_middle (ordinaryFinitePullback A a) (i₁ ≪≫ i₂ ≪≫ i₃).hom
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₁).inv.app L)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a q
      (affineTraceMap k d ≫ vectorIntegrationChart S d F V e) rfl).hom.app
        ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj L))
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₂).inv.app
      ((ordinaryFinitePullback A V.ι).obj L)) hg hinv'

private theorem pulled_chart_coefficient_composition
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (W : Scheme.{u}) (k : W ⟶ V.toScheme) (j : W ⟶ S) (ha : j = k ≫ V.ι) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (affineTraceMap k d) (vectorIntegrationChart S d F V e)).hom.app
        (vectorIntegrationCoefficient A N hA S d F) ≫
      (ordinaryFinitePullback A (affineTraceMap k d)).map
        (((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (vectorIntegrationChart S d F V e) (VectorBundleZeroSection.π S d F)).symm.app
          (affineLinearBaseCoefficient A N hA S d) ≪≫
      (eqToIso (congrArg (ordinaryFinitePullback A)
        (vectorIntegrationChart_isPullback S d F V e).w)).app
          (affineLinearBaseCoefficient A N hA S d) ≪≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (affineTraceProjection V.toScheme d) V.ι).app
          (affineLinearBaseCoefficient A N hA S d) ≪≫
      (ordinaryFinitePullback A (affineTraceProjection V.toScheme d)).mapIso
        (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d) ≪≫
      (affineLinearCoefficientDescent A N hA t V.toScheme
        (affineTracePullbackInvertible N V.ι hS) d).symm)).hom ≫
      (ordinaryFinitePullback A (affineTraceMap k d)).map
        (affineLinearCoefficientDescent A N hA t V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d).hom ≫
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (affineTraceMap_isPullback k d).toCommSq).symm.app
          (affineLinearBaseCoefficient A N hA V.toScheme d)).hom ≫
      (ordinaryFinitePullback A (affineTraceProjection W d)).map
        (vectorIntegrationBaseCoefficientPullback A N hA t k
          (affineTracePullbackInvertible N V.ι hS) d).hom ≫
      (affineLinearCoefficientDescent A N hA t W
        (affineTracePullbackInvertible N j hS) d).symm.hom =
    (vectorIntegrationCartesianCoefficient A N hA t (VectorBundleZeroSection.π S d F)
      j (affineTracePullbackInvertible N j hS) d
      (affineTraceMap k d ≫ vectorIntegrationChart S d F V e)
      (vectorIntegrationPulledChart_isPullback S d F V e W k j ha)
      (affineLinearBaseCoefficient A N hA S d)
      (vectorIntegrationBaseCoefficientPullback A N hA t j hS d)).hom := by
  have _ := hN
  let L := affineLinearBaseCoefficient A N hA S d
  let q := vectorIntegrationChart S d F V e
  let a := affineTraceMap k d
  let r := affineTraceProjection W d
  let sq₁ := (vectorIntegrationChart_isPullback S d F V e).toCommSq
  let sq₂ := (affineTraceMap_isPullback k d).toCommSq
  let sq := (vectorIntegrationPulledChart_isPullback S d F V e W k j ha).toCommSq
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    k V.ι j ha
  let i₁ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q
    (VectorBundleZeroSection.π S d F)).symm.app L
  let i₂ := (eqToIso (congrArg (ordinaryFinitePullback A) sq₁.w)).app L
  let i₃ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (affineTraceProjection V.toScheme d) V.ι).app L
  have hgeom := restricted_chart_geometry A S d F V e W k j ha L
  have h := coefficient_composition
    (ordinaryFinitePullback A V.ι) (ordinaryFinitePullback A k)
    (ordinaryFinitePullback A j) (ordinaryFinitePullback A a)
    (ordinaryFinitePullback A (affineTraceProjection V.toScheme d))
    (ordinaryFinitePullback A r) c
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₂).symm L
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a q
      (affineTraceMap k d ≫ vectorIntegrationChart S d F V e) rfl).hom.app
        ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj L))
    i₁ i₂ i₃
    (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d)
    (vectorIntegrationBaseCoefficientPullback A N hA t k
      (affineTracePullbackInvertible N V.ι hS) d)
    (vectorIntegrationBaseCoefficientPullback A N hA t j hS d)
    (affineLinearCoefficientDescent A N hA t V.toScheme
      (affineTracePullbackInvertible N V.ι hS) d)
    (affineLinearCoefficientDescent A N hA t W
      (affineTracePullbackInvertible N j hS) d)
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm.app L) hgeom
    (orderedTateCoefficientComposition A N hA t k V.ι j ha hS
      (affineTracePullbackInvertible N V.ι hS) d)
  exact h

private theorem pulled_chart_coefficient
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (W : Scheme.{u}) (k : W ⟶ V.toScheme) (j : W ⟶ S) (ha : j = k ≫ V.ι) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (affineTraceMap k d) (vectorIntegrationChart S d F V e)).hom.app
        (vectorIntegrationCoefficient A N hA S d F) ≫
      (ordinaryFinitePullback A (affineTraceMap k d)).map
        (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom ≫
      (affineTraceRightBaseChange A N hA t k
        (affineTracePullbackInvertible N V.ι hS) d (ordinaryFiniteUnit A V.toScheme)).hom ≫
      (affineTraceRight A N hA W d).map
        (ordinaryFiniteUnitPullback A k).hom =
    (vectorIntegrationCartesianCoefficient A N hA t (VectorBundleZeroSection.π S d F)
      j (affineTracePullbackInvertible N j hS) d
      (affineTraceMap k d ≫ vectorIntegrationChart S d F V e)
      (vectorIntegrationPulledChart_isPullback S d F V e W k j ha)
      (affineLinearBaseCoefficient A N hA S d)
      (vectorIntegrationBaseCoefficientPullback A N hA t j hS d)).hom  := by
  unfold vectorIntegrationCartesianCoefficient vectorIntegrationChartCoefficient
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hb := affineTraceRightBaseChange_unit_coefficient A N hA t
    k (affineTracePullbackInvertible N V.ι hS)
      (affineTracePullbackInvertible N j hS) d
  have hb' := congrArg Iso.hom hb
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hb'
  rw [hb']
  simpa only [vectorIntegrationCartesianCoefficient, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] using
    pulled_chart_coefficient_composition N hN A hA t S hS d F V e W k j ha

private theorem exchange_paste_named
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {p : X ⟶ Y} {p' : X' ⟶ Y'} {p'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] [HasCompactification p'] [HasCompactification p'']
    [QuasiCompact p'] [QuasiCompact p'']
    (sq₁ : IsPullback v' p' p v) (sq₂ : IsPullback w' p'' p' w)
    (z : X'' ⟶ X) (c : Y'' ⟶ Y) (hz : z = w' ≫ v') (hc : c = w ≫ v)
    (sq : IsPullback z p'' p c) (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A w).map ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((ordinaryFinitePullback A v').obj K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v c hc).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p'').map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' z hz).hom.app K) := by
  subst hz hc
  exact affineLinearExchange_paste A sq₁ sq₂ K

/-- Restrict the prefix of one frame along an arbitrary map to its frame open.
There is no second frame, linear action, or trace counit in this identity.
Source: blueprint vector-bundle purity proof, paragraph 2, arbitrary base change.
(blueprint: lem-pur-vector-integration-pulled-chart-transport).

Proof: paste the affine-tower base-change square with the inverse-frame square.
Naturality moves the chart coefficient through the tower exchange. The canonical
compact-support comparison intertwines tower exchange and ordinary exchange.
On coefficients, inverse square pasting identifies the two geometric comparisons;
composition of the normalized ordered Tate transport identifies the successive base
coefficients with transport along j. Cancel the intervening isomorphisms. These are
unit and composition equations, so rank zero, empty schemes and zero rings are included.
-/
theorem vectorIntegration_pulled_chart_transport
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (W : Scheme.{u}) [IsNoetherian W] (k : W ⟶ V.toScheme)
    (j : W ⟶ S) (ha : j = k ≫ V.ι) :
    letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
      (vectorIntegration_geometry S d F).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
      (vectorIntegration_geometry S d F).2.1
    letI : TopologicalSpace.NoetherianSpace V.toScheme :=
      V.ι.isOpenEmbedding.isInducing.noetherianSpace
    letI : IsNoetherian V.toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) k V.ι j
      ha).hom.app (vectorIntegrationSource A N hA S d F) ≫
      (ordinaryFinitePullback A k).map
        ((rightDerivedLowerShriekBaseChangeMap A
          (vectorIntegrationChart_isPullback S d F V e)).app
            (vectorIntegrationCoefficient A N hA S d F) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
            (affineTraceProjection V.toScheme d)).map
              (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom ≫
          (affineLinearCompactComparison N hN A hA V.toScheme
            (affineTracePullbackInvertible N V.ι hS) d).inv) ≫
      (affineTraceExchange A k d
        ((affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme)) ≫
        (affineTraceLeft A W d).map
          (affineTraceRightBaseChange A N hA t k
            (affineTracePullbackInvertible N V.ι hS) d (ordinaryFiniteUnit A V.toScheme)).hom ≫
        (affineTraceLeft A W d).map
          ((affineTraceRight A N hA W d).map
            (ordinaryFiniteUnitPullback A k).hom)) =
    vectorIntegrationCartesianPrefix N hN A hA t (VectorBundleZeroSection.π S d F)
      j (affineTracePullbackInvertible N j hS) d
      (affineTraceMap k d ≫ vectorIntegrationChart S d F V e)
      (vectorIntegrationPulledChart_isPullback S d F V e W k j ha)
      (affineLinearBaseCoefficient A N hA S d)
      (vectorIntegrationBaseCoefficientPullback A N hA t j hS d) := by
  let : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).1
  let : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).2.1
  let : IsNoetherian (VectorBundleZeroSection.scheme S d F) :=
    (vectorIntegration_geometry S d F).2.2
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let := affineTraceNoetherian W d
  let := affineTraceNoetherian V.toScheme d
  let K := vectorIntegrationCoefficient A N hA S d F
  let c := vectorIntegrationChartCoefficient A N hA t S hS d F V e
  have hcomp := affineTraceUnitCompactComparison_baseChange N hN A hA t
    k (affineTracePullbackInvertible N V.ι hS) d
  have hn := (rightDerivedLowerShriekBaseChangeMap A
    (affineTraceMap_isPullback k d)).naturality c.hom
  simp only [Functor.comp_map] at hn
  have hp := exchange_paste_named A
    (vectorIntegrationChart_isPullback S d F V e)
    (affineTraceMap_isPullback k d)
    (affineTraceMap k d ≫ vectorIntegrationChart S d F V e) j rfl
    ha
    (vectorIntegrationPulledChart_isPullback S d F V e W k j ha) K
  have hc := pulled_chart_coefficient N hN A hA t S hS d F V e W k j ha
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at hcomp
  unfold vectorIntegrationCartesianPrefix
  simp only [Functor.map_comp, Category.assoc]
  rw [hcomp]
  dsimp only [c, K, ordinaryFinitePullback, vectorIntegrationSource] at hn hp hc ⊢
  rw [reassoc_of% hn]
  rw [reassoc_of% hp]
  simp only [Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc]
  rw [hc]
  rfl

end AlgebraicGeometry.Etale
