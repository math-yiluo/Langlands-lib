/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence

/-! # A descended-coefficient comparison for a Cartesian affine chart

Source: blueprint vector integration, overlap calculation before the counit.
(blueprint: lem-amb-vector-integration-cartesian-prefix-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek affineLinearCompactComparison
  affineLinearCoefficientDescent affineLinearBaseCoefficient
  leftDerivedUpperStarComp derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor

/-- Pull a descended coefficient through a Cartesian chart, then use the fixed tower
coefficient descent. The base coefficient transport is explicit.
Source: blueprint vector integration, canonical coefficient comparison on an overlap.
(blueprint: lem-amb-vector-integration-cartesian-prefix-action). -/
def vectorIntegrationCartesianCoefficient
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X S T : Scheme.{u}} (p : X ⟶ S) (f : T ⟶ S)
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (q : affineTraceTower T d ⟶ X)
    (sq : IsPullback q (affineTraceProjection T d) p f)
    (L : DerivedCategoryModule A S)
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d) :
    (ordinaryFinitePullback A q).obj ((ordinaryFinitePullback A p).obj L) ≅
      (affineTraceRight A N hA T d).obj (ordinaryFiniteUnit A T) :=
  (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app L ≪≫
    (ordinaryFinitePullback A (affineTraceProjection T d)).mapIso b ≪≫
    (affineLinearCoefficientDescent A N hA t T hT d).symm

/-- Exchange for one Cartesian chart with a coefficient descended from its base.
There is no frame and no counit in this construction.
Source: blueprint vector integration, inverse-coordinate comparison.
(blueprint: lem-amb-vector-integration-cartesian-prefix-action). -/
def vectorIntegrationCartesianPrefix
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X S T : Scheme.{u}} [IsNoetherian T] (p : X ⟶ S)
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] [HasCompactification p]
    (f : T ⟶ S) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (q : affineTraceTower T d ⟶ X)
    (sq : IsPullback q (affineTraceProjection T d) p f)
    (L : DerivedCategoryModule A S)
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d) :
    (ordinaryFinitePullback A f).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj
          ((ordinaryFinitePullback A p).obj L)) ⟶
      (affineTraceLeft A T d).obj
        ((affineTraceRight A N hA T d).obj (ordinaryFiniteUnit A T)) :=
  (rightDerivedLowerShriekBaseChangeMap A sq).app _ ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T d)).map
      (vectorIntegrationCartesianCoefficient A N hA t p f hT d q sq L b).hom ≫
    (affineLinearCompactComparison N hN A hA T hT d).inv

private theorem cartesian_coefficient_comp
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X S T : Scheme.{u}} (p : X ⟶ S) (f : T ⟶ S)
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (q : affineTraceTower T d ⟶ X)
    (sq : IsPullback q (affineTraceProjection T d) p f)
    (a : affineTraceTower T d ⟶ affineTraceTower T d)
    (sa : IsPullback a (affineTraceProjection T d) (affineTraceProjection T d) (𝟙 T))
    (sq' : IsPullback (a ≫ q) (affineTraceProjection T d) p f)
    (L : DerivedCategoryModule A S)
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a q).hom.app
        ((ordinaryFinitePullback A p).obj L) ≫
      (ordinaryFinitePullback A a).map
        (vectorIntegrationCartesianCoefficient A N hA t p f hT d q sq L b).hom ≫
      (affineLinearCoefficientPullback A N hA t T hT d a
        (sa.w.trans (Category.comp_id _))).hom =
    (vectorIntegrationCartesianCoefficient A N hA t p f hT d (a ≫ q) sq' L b).hom := by
  let r := affineTraceProjection T d
  have ha : a ≫ r = r := sa.w.trans (Category.comp_id _)
  have hc := leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} A) a q p (a ≫ q) (q ≫ p) ((a ≫ q) ≫ p) rfl rfl rfl L
  have hassoc := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    a r f r (q ≫ p) ((a ≫ q) ≫ p) ha.symm sq.w sq'.w L
  simp only [vectorIntegrationCartesianCoefficient, affineLinearCoefficientPullback,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a r r ha.symm).inv.naturality
    b.hom
  simp only [Functor.comp_map] at hn
  simp only [derivedSquareUpperStarIso]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp,
    Category.assoc, Category.comp_id]
  dsimp only [ordinaryFinitePullback, r] at hn hc hassoc ⊢
  rw [reassoc_of% hn]
  rw [reassoc_of% hc]
  rw [reassoc_of% hassoc]
  simp only [Iso.hom_inv_id_app_assoc]

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

/-- Precomposing a Cartesian chart with a linear automorphism acts on its prefix by
exactly the specified affine trace action. The only geometric hypothesis is equality
of the chart maps; frames, restrictions and existential matrices are absent.
Source: blueprint vector integration overlap calculation, exchange-pasting part.
(blueprint: lem-amb-vector-integration-cartesian-prefix-action).
Proof: inverse-image associativity identifies the two coefficient comparisons.
Paste the chart square with the automorphism square, use exchange naturality for the
coefficient comparison, and cancel the compact-support comparison and identity
inverse-image isomorphisms. -/
theorem vectorIntegrationCartesianPrefix_action
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X S T : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian T]
    (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p]
    (f : T ⟶ S) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (q q' : affineTraceTower T d ⟶ X)
    (sq : IsPullback q (affineTraceProjection T d) p f)
    (sq' : IsPullback q' (affineTraceProjection T d) p f)
    (a : affineTraceTower T d ⟶ affineTraceTower T d)
    (sa : IsPullback a (affineTraceProjection T d) (affineTraceProjection T d) (𝟙 T))
    (hq : q' = a ≫ q) (L : DerivedCategoryModule A S)
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d) :
    vectorIntegrationCartesianPrefix N hN A hA t p f hT d q' sq' L b =
      vectorIntegrationCartesianPrefix N hN A hA t p f hT d q sq L b ≫
        affineLinearTraceAction N hN A hA t T hT d a sa := by
  subst q'
  let := affineTraceNoetherian T d
  let K := (ordinaryFinitePullback A p).obj L
  let E := (rightDerivedLowerShriekBaseChangeMap A sq).app K
  let C := vectorIntegrationCartesianCoefficient A N hA t p f hT d q sq L b
  let R := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T d))
  have hunit :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 T) f f
        (Category.id_comp f).symm).inv.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj K) =
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app _ := by
    apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (𝟙 T) f f (Category.id_comp f).symm).hom.app _)).mp
    simpa only [Iso.hom_inv_id_app, ordinaryFinitePullback] using
      (leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A) f
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj K)).symm
  have hpaste :
      (ordinaryFinitePullback A (𝟙 T)).map E ≫
          (rightDerivedLowerShriekBaseChangeMap A sa).app
            ((ordinaryFinitePullback A q).obj K) =
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 T) f f
          (Category.id_comp f).symm).inv.app _ ≫
          (rightDerivedLowerShriekBaseChangeMap A sq').app K ≫
          R.map ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a q).hom.app K) := by
    exact exchange_paste_named A sq sa (a ≫ q) f rfl (Category.id_comp f).symm sq' K
  rw [hunit] at hpaste
  have hp := congrArg (fun z ↦
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).inv.app _ ≫ z) hpaste
  dsimp only [ordinaryFinitePullback] at hp
  simp only [Iso.inv_hom_id_app_assoc, Functor.comp_obj] at hp
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).inv.naturality E
  simp only [Functor.id_map] at hn
  rw [← reassoc_of% hn] at hp
  have hid : affineLinearPullbackId A T =
      leftDerivedUpperStarId (ModuleCat.{u + 1} A) T := by
    simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
      leftDerivedUpperStarIsoMapDerivedCategory]
  have hcoeff := cartesian_coefficient_comp A N hA t p f hT d q sq a sa sq' L b
  have hnC := (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).inv.naturality
    (R.map C.hom)
  simp only [Functor.id_map] at hnC
  have hnE := (rightDerivedLowerShriekBaseChangeMap A sa).naturality C.hom
  simp only [Functor.comp_map] at hnE
  unfold vectorIntegrationCartesianPrefix affineLinearTraceAction
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hid, ← hcoeff]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [ordinaryFinitePullback] at hnC hnE hp ⊢
  rw [reassoc_of% hnC, reassoc_of% hnE]
  dsimp only [E, K, R, C, ordinaryFinitePullback] at hp ⊢
  rw [reassoc_of% hp]

/-- The inverse frame over V, restricted geometrically to U.
Source: blueprint vector integration, restriction to an overlap.
(blueprint: lem-amb-vector-integration-cartesian-prefix-action). -/
def vectorIntegrationRestrictedChart (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U V : S.Opens) (hUV : U ≤ V)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    affineTraceTower U.toScheme d ⟶ VectorBundleZeroSection.scheme S d F :=
  affineTraceMap (S.homOfLE hUV) d ≫ vectorIntegrationChart S d F V e

/-- The restricted inverse frame still gives a Cartesian square over U into S.
Source: blueprint vector integration, pasting the open restriction square.
(blueprint: lem-amb-vector-integration-cartesian-prefix-action). -/
theorem vectorIntegrationRestrictedChart_isPullback
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U V : S.Opens) (hUV : U ≤ V)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    IsPullback (vectorIntegrationRestrictedChart S d F U V hUV e)
      (affineTraceProjection U.toScheme d) (VectorBundleZeroSection.π S d F) U.ι := by
  simpa only [vectorIntegrationRestrictedChart, S.homOfLE_ι hUV] using
    (affineTraceMap_isPullback (S.homOfLE hUV) d).paste_horiz
      (vectorIntegrationChart_isPullback S d F V e)

end AlgebraicGeometry.Etale
