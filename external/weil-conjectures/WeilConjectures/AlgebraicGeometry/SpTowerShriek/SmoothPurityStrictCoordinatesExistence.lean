/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictBaseCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictGeometricCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOpenTensorCoordinates

/-! # Constant-section coordinates for strict quotient towers

Source: Zheng Construction 4.1 and Lemma 4.10; blueprint tower operations proof (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek
