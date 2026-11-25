/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!

# Uniqueness of refinements out of a dense compactification

If the open immersion `c.i : X ⟶ c.Z` of a compactification `c` of `f : X ⟶ Y` is
scheme-theoretically dominant, i.e. `c` is a *dense* compactification, then there is at most one
refinement of any compactification `d` of `f` by `c`: a refinement is a morphism into `d.Z`,
which is separated over `Y`, and any two refinements agree after composing with `c.i`, since
both composites are `d.i`.

## Main results

- `AlgebraicGeometry.Compactification.Refinement.ext_of_isSchemeTheoreticallyDominant`:
  two refinements of `d` by a dense compactification `c` are equal;
- `AlgebraicGeometry.Compactification.Refinement.instSubsingleton`: the type of refinements of
  `d` by a dense compactification `c` is a subsingleton.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification.Refinement

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}

/-- **Uniqueness of refinements out of a dense compactification**: if the open immersion of the
compactification `c` is scheme-theoretically dominant, then any two refinements of `d` by `c`
are equal. This is what makes the comparison morphism between two compactifications
well defined. (blueprint: `GEO-BA43-DENSE-REFINEMENT-UNIQUENESS`) -/
theorem ext_of_isSchemeTheoreticallyDominant (hc : IsSchemeTheoreticallyDominant c.i)
    (r r' : c.Refinement d) : r = r' := by
  have := hc
  ext
  exact AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant d.g
    (by rw [r.hom_g, r'.hom_g]) c.i (by rw [r.i_hom, r'.i_hom])

/-- The type of refinements of `d` by a dense compactification `c` is a subsingleton. This is
phrased as an instance under an explicit `[IsSchemeTheoreticallyDominant c.i]` binder, since
density of `c` is not findable by typeclass search from `c` alone; with the density instance in
scope it is then found automatically. -/
instance instSubsingleton [IsSchemeTheoreticallyDominant c.i] :
    Subsingleton (c.Refinement d) :=
  ⟨ext_of_isSchemeTheoreticallyDominant ‹_›⟩

end AlgebraicGeometry.Compactification.Refinement
