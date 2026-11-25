/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Compactification.Defs

/-!
# Compactifiable morphisms to locally noetherian schemes are quasi-compact

A compactification `X ⟶[i] Z ⟶[g] Y` of `f : X ⟶ Y` exhibits `X` as an open subscheme of a
scheme `Z` proper (in particular locally of finite type) over `Y`. If `Y` is locally noetherian,
then so is `Z`, and an open immersion into a locally noetherian scheme is quasi-compact
(Stacks, Tag 01OX). Hence `f = i ≫ g` is quasi-compact.

## Main statements

- `AlgebraicGeometry.HasCompactification.quasiCompact`: a compactifiable morphism to a locally
  noetherian scheme is quasi-compact.
- `AlgebraicGeometry.HasCompactification.quasiCompact_of_locallyOfFiniteType`: a compactifiable
  morphism to a scheme locally of finite type over a field is quasi-compact.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A compactifiable morphism to a locally noetherian scheme is quasi-compact: it is an open
immersion into a scheme proper, hence of finite type, over the base, and an open immersion into
a locally noetherian scheme is quasi-compact (Stacks, Tag 01OX). -/
theorem HasCompactification.quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [IsLocallyNoetherian Y] : QuasiCompact f := by
  let c := HasCompactification.compactification f
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  rw [c.comm]
  infer_instance

/-- A compactifiable morphism to a scheme locally of finite type over a field is
quasi-compact. -/
theorem HasCompactification.quasiCompact_of_locallyOfFiniteType {X Y : Scheme.{u}} {k : Type u}
    [Field k] (f : X ⟶ Y) [HasCompactification f] (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] : QuasiCompact f :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  HasCompactification.quasiCompact f

end AlgebraicGeometry
