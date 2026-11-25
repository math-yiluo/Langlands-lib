/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackTriangles
public import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReduction
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
public import WeilConjectures.PoincareDuality.IntegralCompletedComparison.IntegralPullbackCompletedComparisonData
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.IntegralPullbackSignedShift
import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.CompletedIntegralFiniteTowerTransport

set_option linter.privateModule false

/-! # Integral and strict-tower completed pullback

Source: Stacks Project, proetale.tex, Tag 099N(5), with sites-cohomology.tex,
Tag 0941 (blueprint: lem-a1-integral-pullback-completed-comparison).

The coefficient transport is the existing projection-normalized ring isomorphism.
Finite comparisons below are fixed on inverse-image generators; the integral
projections are the actual mapping-cocone projections on K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private instance (priority := 3000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W

private instance (priority := 3000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

namespace WeilConjectures.IntegralCompletedComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

attribute [local irreducible] pbcIntegralDatum

private theorem quotientEquiv_eq (n : ℕ) :
    ImmersionCompletedPullback.quotientEquiv l E n = integralCoefficientULift l E n := by
  exact (ImmersionCompletedPullback.quotientEquiv_exists l E n).unique
    (ImmersionCompletedPullback.quotientEquiv_exists l E n).exists.choose_spec
    (integralCoefficientULift_exists l E n).exists.choose_spec

private theorem coefficientIso_eq (T : Scheme.{u}) :
    (adicLisseForget T).mapIso (ImmersionCompletedPullback.completedRingIso l E T) =
      integralDetailedCoefficientComparison T l E := by
  apply (integralDetailedCoefficientComparison_exists T l E).unique
    ?_ (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec
  intro n
  have h := congrArg (fun f ↦ (adicLisseForget T).map f)
    ((ImmersionCompletedPullback.completedRingIso_exists l E T).exists.choose_spec n)
  have hp : (adicLisseForget T).map
      (completedIntegralCommRingProjectionUnrestricted l E T n) =
      limit.π (integralCoefficientSheafSystem l E T) (op n) := by
    rfl
  simpa only [Functor.map_comp, Functor.mapIso_hom, hp,
    ImmersionCompletedPullback.completedRingIso,
    ImmersionCompletedPullback.finiteRingIso, integralDetailedLevelComparison,
    Iso.trans_hom, Functor.mapIso_trans, quotientEquiv_eq] using h

end WeilConjectures.IntegralCompletedComparison
