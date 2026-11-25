/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationOverlapCoordinates
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRestrictedChartTransport

/-! # The change of frame before applying the affine counit

Source: blueprint sec-smooth-purity/sk-prop-an/def-amb-vector-integration.proof.md,
overlap calculation, and proposition-purity-vector-bundles.
(blueprint: lem-amb-vector-integration-overlap-chart-prefix).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Exchange and coefficient transport for the affine tower at the constant object.
This comparison contains neither a projective-line datum nor its counit.
Source: blueprint affine trace construction, base-change comparison in Step 6.
(blueprint: lem-amb-vector-integration-overlap-chart-prefix). -/
def affineTraceUnitBaseChange (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {T S : Scheme.{u}} (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A f).obj ((affineTraceLeft A S d).obj
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ⟶
    (affineTraceLeft A T d).obj
      ((affineTraceRight A N hA T d).obj (ordinaryFiniteUnit A T)) :=
  affineTraceExchange A f d ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
    (affineTraceLeft A T d).map
      (affineTraceRightBaseChange A N hA t f hS d (ordinaryFiniteUnit A S)).hom ≫
    (affineTraceLeft A T d).map
      ((affineTraceRight A N hA T d).map (ordinaryFiniteUnitPullback A f).hom)

/-- The actual inverse-frame exchange and coefficient comparison, stopping before the
counit. This is exactly the first three factors of vectorIntegrationLocalTrace.
Source: blueprint vector integration, prescribed local map.
(blueprint: lem-amb-vector-integration-overlap-chart-prefix). -/
def vectorIntegrationChartPrefix (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :
    (ordinaryFinitePullback A V.ι).obj (vectorIntegrationSource A N hA S d F) ⟶
      (affineTraceLeft A V.toScheme d).obj
        ((affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme)) :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).2.1
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  (rightDerivedLowerShriekBaseChangeMap A
      (vectorIntegrationChart_isPullback S d F V e)).app
        (vectorIntegrationCoefficient A N hA S d F) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection V.toScheme d)).map
      (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom ≫
    (affineLinearCompactComparison N hN A hA V.toScheme
      (affineTracePullbackInvertible N V.ι hS) d).inv

/-- Restrict a frame comparison to a smaller open and transport its affine tower there.
The source compositor uses the specified equality of the open inclusions.
Source: blueprint vector integration, restriction to an overlap.
(blueprint: lem-amb-vector-integration-overlap-chart-prefix). -/
def vectorIntegrationOverlapPrefix (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (U V : S.Opens) (hUV : U ≤ V)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    (ordinaryFinitePullback A U.ι).obj (vectorIntegrationSource A N hA S d F) ⟶
      (affineTraceLeft A U.toScheme d).obj
        ((affineTraceRight A N hA U.toScheme d).obj (ordinaryFiniteUnit A U.toScheme)) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (S.homOfLE hUV) V.ι U.ι
    (S.homOfLE_ι hUV).symm).hom.app (vectorIntegrationSource A N hA S d F) ≫
    (ordinaryFinitePullback A (S.homOfLE hUV)).map
      (vectorIntegrationChartPrefix N hN A hA t S hS d F V e) ≫
    affineTraceUnitBaseChange A N hA t (S.homOfLE hUV)
      (affineTracePullbackInvertible N V.ι hS) d

/-- On a common smaller open the two inverse-frame comparisons differ by the actual
linear-coordinate pullback action. No counit, projective-line datum, sheaf Hom
correspondence, or descent assertion occurs in this statement.
Source: blueprint vector integration, overlap calculation, and linear-trace invariance,
coordinate convention; original local-compatibility proof Steps 1--2.
(blueprint: lem-amb-vector-integration-overlap-chart-prefix).

Proof: restrict both module frames to U using the restriction functor on module sheaves
and its free-module comparison. Their composite is an automorphism of the free module.
Its images of the standard global basis give a matrix G of global sections with inverse
obtained from the inverse automorphism, as in transition_spec. In the convention
 e'_j = sum_i G_ij e_i the coordinate change is G transpose. Thus the inverse charts
are related by g = (G transpose) inverse. Check this equality on degree-one generators
of the symmetric algebra and then use its universal property. The corresponding
linear map is affineTraceLinearMap, and its square over the identity is Cartesian.
Paste each restricted inverse-coordinate square with its original chart square.
Compact-support exchange pasting, its naturality in the coefficient, and naturality
of the bounded/unbounded compact-support comparisons identify the two resulting
prefixes. Associativity of inverse-image compositors and the composition equations
of normalized Tate pullback identify the coefficient factors: they are exactly
vectorIntegrationChartCoefficient and affineTraceRightBaseChange followed by the
constant-unit comparison in affineTraceUnitBaseChange. The remaining automorphism
factor, conjugated by affineLinearCompactComparison, is precisely
affineLinearTraceAction (with no counit applied). This proves the displayed equation.
For rank zero the basis and matrix are empty and all these equations are unit equations;
restriction to the empty open and the zero coefficient ring obey the same formulas.
-/
theorem vectorIntegration_overlap_chart_prefix (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (U V V' : S.Opens) (hUV : U ≤ V) (hUV' : U ≤ V')
    (e : VectorBundleZeroSection.Trivialization S d F V)
    (e' : VectorBundleZeroSection.Trivialization S d F V') :
    letI : TopologicalSpace.NoetherianSpace U.toScheme :=
      U.ι.isOpenEmbedding.isInducing.noetherianSpace
    letI : IsNoetherian U.toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    ∃ g : Matrix.GeneralLinearGroup (Fin d) Γ(U.toScheme, ⊤),
      vectorIntegrationOverlapPrefix N hN A hA t S hS d F U V' hUV' e' =
        vectorIntegrationOverlapPrefix N hN A hA t S hS d F U V hUV e ≫
          affineLinearTraceAction N hN A hA t U.toScheme
            (affineTracePullbackInvertible N U.ι hS) d
            (affineTraceLinearMap U.toScheme d g) (affineTraceLinearMap_isPullback _ _ g) := by
  let : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian U.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let := (vectorIntegration_geometry S d F).1
  let := (vectorIntegration_geometry S d F).2.1
  let := (vectorIntegration_geometry S d F).2.2
  obtain ⟨g, hg⟩ := vectorIntegration_overlap_coordinates S d F U V V' hUV hUV' e e'
  refine ⟨g, ?_⟩
  have hV := vectorIntegration_restricted_chart_transport N hN A hA t S hS d F U V hUV e
  have hV' := vectorIntegration_restricted_chart_transport N hN A hA t S hS d F U V' hUV' e'
  change vectorIntegrationOverlapPrefix N hN A hA t S hS d F U V hUV e = _ at hV
  change vectorIntegrationOverlapPrefix N hN A hA t S hS d F U V' hUV' e' = _ at hV'
  rw [hV', hV]
  exact vectorIntegrationCartesianPrefix_action N hN A hA t (VectorBundleZeroSection.π S d F)
    U.ι (affineTracePullbackInvertible N U.ι hS) d _ _
    (vectorIntegrationRestrictedChart_isPullback S d F U V hUV e)
    (vectorIntegrationRestrictedChart_isPullback S d F U V' hUV' e')
    (affineTraceLinearMap U.toScheme d g) (affineTraceLinearMap_isPullback _ _ g) hg
    (affineLinearBaseCoefficient A N hA S d)
    (vectorIntegrationBaseCoefficientPullback A N hA t U.ι hS d)

end AlgebraicGeometry.Etale
