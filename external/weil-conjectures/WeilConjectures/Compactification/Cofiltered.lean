/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Compactification.RefinementUniqueness

/-!

# The category of compactifications is cofiltered

The compactifications of a fixed morphism `f : X ⟶ Y` form a category
`AlgebraicGeometry.Compactification.category`, with the refinements of
`WeilConjectures.Compactification.Refinement` as morphisms. This file shows that this
category is cofiltered as soon as `f` is quasi-compact and admits a compactification.

Both halves come from the *dense* common refinement
`AlgebraicGeometry.Compactification.exists_common_refinement_isSchemeTheoreticallyDominant`,
which refines two given compactifications by one in which `X` is scheme-theoretically
dense:

- any two compactifications are refined by a common one, which is the cone on two objects;
- any two parallel refinements `r s : c ⟶ d` are equalized by a further refinement. No
  equalizer subscheme has to be built for this: a refinement out of a scheme-theoretically
  dense compactification is unique (`Refinement.ext_of_isSchemeTheoreticallyDominant`), so
  for a dense `e` refining `c` by `h : e ⟶ c` the two composites `h ≫ r` and `h ≫ s` are
  refinements of `d` by `e`, hence literally equal.

## Main results

- `AlgebraicGeometry.Compactification.isCofilteredOrEmpty`: the category of
  compactifications of a quasi-compact morphism is cofiltered or empty;
- `AlgebraicGeometry.Compactification.isCofiltered`: it is cofiltered as soon as a
  compactification exists.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Blueprint `proposition-dense-compactifications-form-cofiltered-category`: The compactification
category and common refinements.

For a quasi-compact `f : X ⟶ Y`, the category of compactifications of `f` is cofiltered or
empty: any two compactifications `c` and `d` admit a common refinement `e`, and any two
parallel refinements `r s : c ⟶ d` are equalized by a further refinement `h : e ⟶ c`.

```text
      e            e ──h──→ c ⇉ d
    ╱   ╲                  r s
   ↙     ↘         with  h ≫ r = h ≫ s
  c       d
```
-/
instance isCofilteredOrEmpty [QuasiCompact f] :
    IsCofilteredOrEmpty (Compactification f) where
  cone_objs c d :=
    let ⟨e, ⟨r⟩, ⟨s⟩⟩ := exists_common_refinement c d
    ⟨e, r, s, trivial⟩
  cone_maps c d r s := by
    obtain ⟨e, he, ⟨h⟩, -⟩ := exists_common_refinement_isSchemeTheoreticallyDominant c c
    have := he
    exact ⟨e, h, Subsingleton.elim (α := e.Refinement d) _ _⟩

/-- Blueprint `proposition-dense-compactifications-form-cofiltered-category`: The compactification
category is cofiltered.

For a quasi-compact `f : X ⟶ Y` admitting a compactification, the category of
compactifications of `f` is cofiltered: it is nonempty and cofiltered or empty. -/
instance isCofiltered [QuasiCompact f] [HasCompactification f] :
    IsCofiltered (Compactification f) where
  nonempty := HasCompactification.nonempty_compactification

end AlgebraicGeometry.Compactification
