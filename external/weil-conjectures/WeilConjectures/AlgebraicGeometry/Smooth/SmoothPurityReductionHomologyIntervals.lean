/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTorAmplitude
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

/-! Cohomological support transport for the normalized smooth-purity reduction tower.
Source: blueprint latest, normalized-towers, uniform Tor and cohomological bounds.
(blueprint: lem-sp-reduction-tower-tor-intervals).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

end AlgebraicGeometry.ProEtale
