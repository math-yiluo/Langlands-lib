/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefix
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceUnitCompactBaseChange
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRestrictedChartCoefficient

/-! # Restriction of one vector integration chart comparison

Source: blueprint vector integration, overlap calculation, exchange-pasting part.
(blueprint: lem-amb-vector-integration-restricted-chart-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek affineLinearCompactComparison
  affineLinearCoefficientDescent affineLinearBaseCoefficient
  leftDerivedUpperStarComp derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory

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

/-- Restricting the prefix for a single frame is exchange for the composite inverse
chart with its coefficient descended directly from the base. There is no second frame,
change-of-frame matrix, action or trace counit in this assertion.
Source: blueprint sec-smooth-purity/sk-prop-an/def-amb-vector-integration.proof.md,
restriction to an overlap, original overlap-chart-prefix proof Steps 3--4.
(blueprint: lem-amb-vector-integration-restricted-chart-transport).

Proof: paste the Cartesian tower square for U into V with the inverse-frame square.
Horizontal compact-support exchange pasting identifies the two exchange factors;
naturality moves the pulled-back chart coefficient through the second exchange.
Naturality of the bounded-below/unbounded compact-support comparisons changes the
tower exchange into the ordinary compact-support exchange. On coefficients expand
vectorIntegrationChartCoefficient and affineTraceRightBaseChange. Associativity of
inverse-image compositors and the composition law of the normalized Tate transport
identify the successive pullbacks with the direct pullback along U into S. Prove this
coefficient identity by induction on d: the zero stage is the constant-unit pullback
composition identity; the successor uses tensor-pullback composition and the normalized
shifted-line pullback composition equation. The resulting comparison is precisely the
inverse square isomorphism, pullback of vectorIntegrationBaseCoefficientPullback, and
inverse affineLinearCoefficientDescent defining vectorIntegrationCartesianCoefficient.
The final compact-support comparison is the one over U. Associativity and cancellation
of the intervening isomorphisms give the formula. These same identities cover d=0,
empty opens and the zero coefficient ring. -/
theorem vectorIntegration_restricted_chart_transport
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U V : S.Opens) (hUV : U ≤ V)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
      (vectorIntegration_geometry S d F).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
      (vectorIntegration_geometry S d F).2.1
    letI : TopologicalSpace.NoetherianSpace U.toScheme :=
      U.ι.isOpenEmbedding.isInducing.noetherianSpace
    letI : IsNoetherian U.toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    letI : TopologicalSpace.NoetherianSpace V.toScheme :=
      V.ι.isOpenEmbedding.isInducing.noetherianSpace
    letI : IsNoetherian V.toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (S.homOfLE hUV) V.ι U.ι
      (S.homOfLE_ι hUV).symm).hom.app (vectorIntegrationSource A N hA S d F) ≫
      (ordinaryFinitePullback A (S.homOfLE hUV)).map
        ((rightDerivedLowerShriekBaseChangeMap A
          (vectorIntegrationChart_isPullback S d F V e)).app
            (vectorIntegrationCoefficient A N hA S d F) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
            (affineTraceProjection V.toScheme d)).map
              (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom ≫
          (affineLinearCompactComparison N hN A hA V.toScheme
            (affineTracePullbackInvertible N V.ι hS) d).inv) ≫
      (affineTraceExchange A (S.homOfLE hUV) d
        ((affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme)) ≫
        (affineTraceLeft A U.toScheme d).map
          (affineTraceRightBaseChange A N hA t (S.homOfLE hUV)
            (affineTracePullbackInvertible N V.ι hS) d (ordinaryFiniteUnit A V.toScheme)).hom ≫
        (affineTraceLeft A U.toScheme d).map
          ((affineTraceRight A N hA U.toScheme d).map
            (ordinaryFiniteUnitPullback A (S.homOfLE hUV)).hom)) =
    vectorIntegrationCartesianPrefix N hN A hA t (VectorBundleZeroSection.π S d F)
      U.ι (affineTracePullbackInvertible N U.ι hS) d
      (vectorIntegrationRestrictedChart S d F U V hUV e)
      (vectorIntegrationRestrictedChart_isPullback S d F U V hUV e)
      (affineLinearBaseCoefficient A N hA S d)
      (vectorIntegrationBaseCoefficientPullback A N hA t U.ι hS d) := by
  let : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).1
  let : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).2.1
  let : IsNoetherian (VectorBundleZeroSection.scheme S d F) :=
    (vectorIntegration_geometry S d F).2.2
  let : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian U.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let := affineTraceNoetherian U.toScheme d
  let := affineTraceNoetherian V.toScheme d
  let K := vectorIntegrationCoefficient A N hA S d F
  let c := vectorIntegrationChartCoefficient A N hA t S hS d F V e
  have hcomp := affineTraceUnitCompactComparison_baseChange N hN A hA t
    (S.homOfLE hUV) (affineTracePullbackInvertible N V.ι hS) d
  have hn := (rightDerivedLowerShriekBaseChangeMap A
    (affineTraceMap_isPullback (S.homOfLE hUV) d)).naturality c.hom
  simp only [Functor.comp_map] at hn
  have hp := exchange_paste_named A
    (vectorIntegrationChart_isPullback S d F V e)
    (affineTraceMap_isPullback (S.homOfLE hUV) d)
    (vectorIntegrationRestrictedChart S d F U V hUV e) U.ι rfl
    (S.homOfLE_ι hUV).symm
    (vectorIntegrationRestrictedChart_isPullback S d F U V hUV e) K
  have hc := vectorIntegration_restricted_chart_coefficient N hN A hA t S hS d F U V hUV e
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at hcomp
  unfold vectorIntegrationCartesianPrefix
  simp only [Functor.map_comp, Category.assoc]
  rw [hcomp]
  dsimp only [c, K, ordinaryFinitePullback, vectorIntegrationSource] at hn hp hc ⊢
  rw [reassoc_of% hn]
  rw [reassoc_of% hp]
  simp only [Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc]
  dsimp only [vectorIntegrationRestrictedChart] at hc ⊢
  rw [hc]
  rfl

end AlgebraicGeometry.Etale
