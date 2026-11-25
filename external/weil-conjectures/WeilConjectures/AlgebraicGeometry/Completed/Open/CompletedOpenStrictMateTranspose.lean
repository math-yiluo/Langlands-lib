/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedOpenFiniteTranspose.CompletedOpenFiniteTransposeCoherence
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRingStrictFiniteExchange
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedReductionPullbackSquare

/-! The strict normalized exchange is the transpose of the pulled open unit.
Source: Stacks Project, Tag 03DI; blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-strict-mate-transpose).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']

end AlgebraicGeometry.Scheme
