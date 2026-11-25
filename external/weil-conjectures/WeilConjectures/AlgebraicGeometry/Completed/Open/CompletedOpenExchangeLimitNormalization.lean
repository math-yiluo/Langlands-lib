/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRingStrictFiniteExchange
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransportLemma
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import WeilConjectures.AlgebraicGeometry.Completed.CompletedStrictOpenExchange

/-! Normalization of completed open exchange by the simultaneous strict exchange.
Source: Stacks Tags 03DI and 091N; the finite-exchange and final-limit paragraphs.
(blueprint: lem-cbc-completed-open-exchange-limit-normalization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']

end AlgebraicGeometry.Scheme
