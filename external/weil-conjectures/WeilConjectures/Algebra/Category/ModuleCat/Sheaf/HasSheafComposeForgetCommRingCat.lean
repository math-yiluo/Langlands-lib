/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Algebra.Category.Ring.Limits

/-! # Composing sheaves of commutative rings with the forgetful functor to rings

The instance `(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat)` is found
by Mathlib's general instances, but when the term `sheafCompose (Opens.grothendieckTopology X)
(forget₂ CommRingCat RingCat)` appears in the statement of a theorem (typically in a hypothesis
`R = (sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf` for a ringed space `X`), the search
can get stuck on universe constraints and never terminate (Mathlib v4.35.0). This file states the
instance directly for sheaves on a topological space, so that the search succeeds at once.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace

namespace SheafOfModules

/-- Composition with the forgetful functor from commutative rings to rings preserves sheaves on a
topological space (stated directly so that instance search does not get stuck on universe
constraints while theorem statements mentioning it are elaborated). -/
instance instHasSheafComposeForgetCommRingCat (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  inferInstance

end SheafOfModules
