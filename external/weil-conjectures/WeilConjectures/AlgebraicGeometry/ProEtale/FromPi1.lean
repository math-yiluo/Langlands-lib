/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RingHom.Smooth

/-!
# Etale

Ported from the `proetale` package (`Proetale.FromPi1.Etale`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

-- This exists in Pi1 and is being upstreamed to mathlib.
instance {X Y : Scheme} (f : X ⟶ Y) [Etale f] : Flat f :=
  inferInstance

end AlgebraicGeometry
