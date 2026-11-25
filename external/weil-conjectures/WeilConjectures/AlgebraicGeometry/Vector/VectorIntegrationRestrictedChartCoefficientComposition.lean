/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefix
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateExactOpenComposition
import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube

/-! # Geometric coefficient composition after tower descent

(blueprint: lem-amb-vector-integration-restricted-chart-coefficient-composition).
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

private lemma uncompared_composite
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : C ⥤ E}
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H') (k : H' ≅ F' ⋙ G')
    {K : C} {B : D} {V : E} (a : F.obj K ⟶ B) (b : G.obj B ⟶ V)
    (d : H.obj K ⟶ V)
    (hc : k.inv.app K ≫ eH.inv.app K ≫ d =
      G'.map (eF.inv.app K ≫ a) ≫ eG.inv.app B ≫ b) :
    (eH ≪≫ k ≪≫ Functor.isoWhiskerRight eF.symm G' ≪≫
        Functor.isoWhiskerLeft F eG.symm).hom.app K ≫ G.map a ≫ b = d := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc]
  rw [← eG.inv.naturality_assoc, ← G'.map_comp_assoc, ← hc]
  simp only [Iso.hom_inv_id_app_assoc]

private lemma upperStar_comp_transport (A : Type (u + 1)) [CommRing A]
    {T U S : Scheme.{u}} (p : T ⟶ U) (v : U ⟶ S) (w : T ⟶ S)
    (hw : w = p ≫ v) :
    (upperStarComp (ModuleCat.{u + 1} A) p v).symm ≪≫
        eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) hw.symm) =
      (upperStarComp (ModuleCat.{u + 1} A) p v w hw).symm := by
  subst w
  simp only [eqToIso_refl, Iso.trans_refl]

private lemma open_comp_eq (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {U V : X.Opens} (h : U ≤ V) :
    DegreeZeroMapGluing.openComp
        (fun T : Scheme.{u} ↦ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (fun {_ _} j ↦ upperStar (ModuleCat.{u + 1} A) j)
        (fun {_ _ _} i j ↦ upperStarComp (ModuleCat.{u + 1} A) i j) X h =
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) (X.homOfLE h) V.ι U.ι
          (Scheme.homOfLE_ι X h).symm) ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} A) V.ι)
          (upperStar (ModuleCat.{u + 1} A) (X.homOfLE h))).symm).symm := by
  unfold DegreeZeroMapGluing.openComp
  rw [upperStar_comp_transport A (X.homOfLE h) V.ι U.ι
    (X.homOfLE_ι h).symm, Iso.trans_symm]
  apply congrArg (fun c ↦ _ ≪≫ c)
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_symm _

private lemma base_coefficient_comp (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    {U V : S.Opens} (hUV : U ≤ V) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (S.homOfLE hUV) V.ι U.ι
      (S.homOfLE_ι hUV).symm).hom.app (affineLinearBaseCoefficient A N hA S d) ≫
      (ordinaryFinitePullback A (S.homOfLE hUV)).map
        (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d).hom ≫
      (vectorIntegrationBaseCoefficientPullback A N hA t (S.homOfLE hUV)
        (affineTracePullbackInvertible N V.ι hS) d).hom =
      (vectorIntegrationBaseCoefficientPullback A N hA t U.ι hS d).hom := by
  have h := congrArg Iso.hom (orderedTateExactOpenComposition A N hA t S hS d hUV
    (affineTracePullbackInvertible N V.ι hS))
  rw [open_comp_eq] at h
  simp only [orderedTateExactPullback, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom] at h
  have hc := uncompared_composite
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) V.ι)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (S.homOfLE hUV))
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) U.ι)
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) (S.homOfLE hUV) V.ι U.ι
        (S.homOfLE_ι hUV).symm) ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm)
    (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d).hom
    (vectorIntegrationBaseCoefficientPullback A N hA t (S.homOfLE hUV)
      (affineTracePullbackInvertible N V.ι hS) d).hom
    (vectorIntegrationBaseCoefficientPullback A N hA t U.ι hS d).hom h
  simpa only [ordinaryFinitePullback, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
      Iso.trans_assoc, Iso.symm_self_id_assoc] using hc

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
    (U V : S.Opens) (hUV : U ≤ V)
    (e : VectorBundleZeroSection.Trivialization S d F V)
    (L : DerivedCategoryModule A S) :
    let q := vectorIntegrationChart S d F V e
    let a := affineTraceMap (S.homOfLE hUV) d
    let r := affineTraceProjection U.toScheme d
    let sq₁ := (vectorIntegrationChart_isPullback S d F V e).toCommSq
    let sq₂ := (affineTraceMap_isPullback (S.homOfLE hUV) d).toCommSq
    let sq := (vectorIntegrationRestrictedChart_isPullback S d F U V hUV e).toCommSq
    let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (S.homOfLE hUV) V.ι U.ι (S.homOfLE_ι hUV).symm
    let i₁ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q
      (VectorBundleZeroSection.π S d F)).symm.app L
    let i₂ := (eqToIso (congrArg (ordinaryFinitePullback A) sq₁.w)).app L
    let i₃ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (affineTraceProjection V.toScheme d) V.ι).app L
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a q
      (vectorIntegrationRestrictedChart S d F U V hUV e) rfl).hom.app
        ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj L) ≫
      (ordinaryFinitePullback A a).map (i₁ ≪≫ i₂ ≪≫ i₃).hom ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₂).inv.app
        ((ordinaryFinitePullback A V.ι).obj L) =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app L ≫
      (ordinaryFinitePullback A r).map (c.hom.app L) := by
  let q := vectorIntegrationChart S d F V e
  let a := affineTraceMap (S.homOfLE hUV) d
  let r := affineTraceProjection U.toScheme d
  let sq₁ := (vectorIntegrationChart_isPullback S d F V e).toCommSq
  let sq₂ := (affineTraceMap_isPullback (S.homOfLE hUV) d).toCommSq
  let sq := (vectorIntegrationRestrictedChart_isPullback S d F U V hUV e).toCommSq
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (S.homOfLE hUV) V.ι U.ι (S.homOfLE_ι hUV).symm
  have hp := derivedSquareUpperStarIso_paste (ModuleCat.{u + 1} A) sq₁ sq₂ sq
    rfl (S.homOfLE_ι hUV).symm L
  have hinv' :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a q
        (vectorIntegrationRestrictedChart S d F U V hUV e) rfl).hom.app
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
        (vectorIntegrationRestrictedChart S d F U V hUV e) rfl).symm.app
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
      (vectorIntegrationRestrictedChart S d F U V hUV e) rfl).hom.app
        ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj L))
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₂).inv.app
      ((ordinaryFinitePullback A V.ι).obj L)) hg hinv'

/-- Coefficient descent for a frame restricted through two nested opens.
Source: blueprint vector integration, overlap calculation.
(blueprint: lem-amb-vector-integration-restricted-chart-coefficient-composition).

Proof: cancel the affine descent over V and identify the chart's explicit
compositor with its inverse square comparison. Paste the chart and tower squares,
take inverses, and cancel the mapped inverse base compositor. Naturality moves
coefficient transport through the tower square. Finally the proved ordered Tate
transport composition equation identifies the two base transports with transport
along U into S, leaving the inverse affine descent over U. -/
theorem vectorIntegration_restricted_chart_coefficient_composition
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U V : S.Opens) (hUV : U ≤ V)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (affineTraceMap (S.homOfLE hUV) d) (vectorIntegrationChart S d F V e)).hom.app
        (vectorIntegrationCoefficient A N hA S d F) ≫
      (ordinaryFinitePullback A (affineTraceMap (S.homOfLE hUV) d)).map
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
      (ordinaryFinitePullback A (affineTraceMap (S.homOfLE hUV) d)).map
        (affineLinearCoefficientDescent A N hA t V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d).hom ≫
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (affineTraceMap_isPullback (S.homOfLE hUV) d).toCommSq).symm.app
          (affineLinearBaseCoefficient A N hA V.toScheme d)).hom ≫
      (ordinaryFinitePullback A (affineTraceProjection U.toScheme d)).map
        (vectorIntegrationBaseCoefficientPullback A N hA t (S.homOfLE hUV)
          (affineTracePullbackInvertible N V.ι hS) d).hom ≫
      (affineLinearCoefficientDescent A N hA t U.toScheme
        (affineTracePullbackInvertible N U.ι hS) d).symm.hom =
    (vectorIntegrationCartesianCoefficient A N hA t (VectorBundleZeroSection.π S d F)
      U.ι (affineTracePullbackInvertible N U.ι hS) d
      (vectorIntegrationRestrictedChart S d F U V hUV e)
      (vectorIntegrationRestrictedChart_isPullback S d F U V hUV e)
      (affineLinearBaseCoefficient A N hA S d)
      (vectorIntegrationBaseCoefficientPullback A N hA t U.ι hS d)).hom := by
  have _ := hN
  let L := affineLinearBaseCoefficient A N hA S d
  let q := vectorIntegrationChart S d F V e
  let a := affineTraceMap (S.homOfLE hUV) d
  let r := affineTraceProjection U.toScheme d
  let sq₁ := (vectorIntegrationChart_isPullback S d F V e).toCommSq
  let sq₂ := (affineTraceMap_isPullback (S.homOfLE hUV) d).toCommSq
  let sq := (vectorIntegrationRestrictedChart_isPullback S d F U V hUV e).toCommSq
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (S.homOfLE hUV) V.ι U.ι (S.homOfLE_ι hUV).symm
  let i₁ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q
    (VectorBundleZeroSection.π S d F)).symm.app L
  let i₂ := (eqToIso (congrArg (ordinaryFinitePullback A) sq₁.w)).app L
  let i₃ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (affineTraceProjection V.toScheme d) V.ι).app L
  have hgeom := restricted_chart_geometry A S d F U V hUV e L
  have h := coefficient_composition
    (ordinaryFinitePullback A V.ι) (ordinaryFinitePullback A (S.homOfLE hUV))
    (ordinaryFinitePullback A U.ι) (ordinaryFinitePullback A a)
    (ordinaryFinitePullback A (affineTraceProjection V.toScheme d))
    (ordinaryFinitePullback A r) c
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₂).symm L
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a q
      (vectorIntegrationRestrictedChart S d F U V hUV e) rfl).hom.app
        ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj L))
    i₁ i₂ i₃
    (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d)
    (vectorIntegrationBaseCoefficientPullback A N hA t (S.homOfLE hUV)
      (affineTracePullbackInvertible N V.ι hS) d)
    (vectorIntegrationBaseCoefficientPullback A N hA t U.ι hS d)
    (affineLinearCoefficientDescent A N hA t V.toScheme
      (affineTracePullbackInvertible N V.ι hS) d)
    (affineLinearCoefficientDescent A N hA t U.toScheme
      (affineTracePullbackInvertible N U.ι hS) d)
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm.app L) hgeom
    (base_coefficient_comp A N hA t S hS d hUV)
  exact h

end AlgebraicGeometry.Etale
