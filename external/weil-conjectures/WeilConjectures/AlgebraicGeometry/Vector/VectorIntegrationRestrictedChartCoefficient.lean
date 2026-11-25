/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefix
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRestrictedChartCoefficientCore
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRestrictedChartCoefficientComposition

/-! # Coefficient comparison for a restricted inverse frame

Source: blueprint vector integration, overlap calculation, Tate coefficient transport.
(blueprint: lem-amb-vector-integration-restricted-chart-coefficient).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Successive inverse-image coefficient identifications for a frame on V and its
restriction to U equal direct coefficient descent in the pasted inverse-chart square.
No compact-support functor or exchange map occurs in this equality.
Source: blueprint sec-smooth-purity/sk-prop-an/def-amb-vector-integration.proof.md,
overlap calculation, associativity of the canonical Tate coefficient identifications.
(blueprint: lem-amb-vector-integration-restricted-chart-coefficient).

Proof: expand vectorIntegrationChartCoefficient, affineTraceRightBaseChange and the
Cartesian coefficient. Compose both sides with affineLinearCoefficientDescent over U.
Expand the coefficient descent over V, and use naturality of inverse-image composition
to move the base coefficient comparison past the affine tower square. Induct on d to
identify inverse image of the ordered tensor coefficient with its direct comparison.
At zero this is the constant-unit pullback composition equation. At a successor use
monoidality of derived inverse-image composition and naturality of tensor pullback;
the shifted-line comparison respects composition because normalized roots and Tate-line
comparisons respect composition and derived inverse image commutes with shift. This
also identifies the right-functor base-change map with descent of the base tensor.
Associativity of the inverse-image compositor pastes the inverse-frame square and the
tower square. The equalities of the open inclusions identify the resulting base map
with U.ι. Cancel the coefficient descent over U to obtain the formula. These are
canonical unit, tensor and composition identities, valid for d=0, empty opens and
the zero ring without a choice of orientation. -/
theorem vectorIntegration_restricted_chart_coefficient
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
        (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom ≫
      (affineTraceRightBaseChange A N hA t (S.homOfLE hUV)
        (affineTracePullbackInvertible N V.ι hS) d (ordinaryFiniteUnit A V.toScheme)).hom ≫
      (affineTraceRight A N hA U.toScheme d).map
        (ordinaryFiniteUnitPullback A (S.homOfLE hUV)).hom =
    (vectorIntegrationCartesianCoefficient A N hA t (VectorBundleZeroSection.π S d F)
      U.ι (affineTracePullbackInvertible N U.ι hS) d
      (vectorIntegrationRestrictedChart S d F U V hUV e)
      (vectorIntegrationRestrictedChart_isPullback S d F U V hUV e)
      (affineLinearBaseCoefficient A N hA S d)
      (vectorIntegrationBaseCoefficientPullback A N hA t U.ι hS d)).hom  := by
  unfold vectorIntegrationCartesianCoefficient vectorIntegrationChartCoefficient
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hb := affineTraceRightBaseChange_unit_coefficient A N hA t
    (S.homOfLE hUV) (affineTracePullbackInvertible N V.ι hS)
      (affineTracePullbackInvertible N U.ι hS) d
  have hb' := congrArg Iso.hom hb
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hb'
  rw [hb']
  simpa only [vectorIntegrationCartesianCoefficient, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] using
    vectorIntegration_restricted_chart_coefficient_composition N hN A hA t S hS d F U V hUV e

end AlgebraicGeometry.Etale
