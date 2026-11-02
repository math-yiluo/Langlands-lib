# Empty tails and descending first-level induction

This internal construction organizes the finite descending induction in the
proof route for Stacks Proposition 70.8.1, Tag 07SU, in the registered source
`stacks-noetherian-approximation-2026-11-01`. Its finite tuple presentations
come from the proved constructions motivated by Tag 0BBN in the registered
source `stacks-stratification-2026-11-02`. The successor step explicitly
requires a system on the actual next-threshold restriction. This module
does not construct that system or prove the unconditional first-level
statement.

`affineFiniteTypeFirstLevel_of_isEmpty` takes any étale equivalence relation
whose object scheme has no points. Its arrow scheme also has no points,
because its source map takes values in the empty object scheme. Both schemes
are affine. The object's map to the terminal scheme is an open immersion,
hence locally of finite type. The relation itself, with its identity cartesian
comparison, therefore supplies an affine finite type first level.

`tupleTailPresentation_object_isEmpty` proves that the tail of the family
indexed by lengths zero through `N`, starting at `N+1`, has no object points.
The indexing subtype is empty by the strict bound in `Fin (N+1)`. The
coproduct's standard open cover assigns every hypothetical object point
an index in that empty type, a contradiction. This assertion does not require
a bound on the original relation's tuple lengths.

`tupleTailEmptyFirstLevel` applies the empty-object construction to that
empty tail.

`nonempty_affineFiniteTypeFirstLevel_of_tupleTail_systems` assumes that for
every `p < N+1`, a first level of the higher tail starting at `p+1` supplies
a finite type cartesian system on the actual next-threshold restriction of
the lower tail starting at `p`. Descending induction starts with the empty
tail and applies the previously proved open-extension and actual-tail
recovery theorem at each step. The resulting first level of the zero tail
then transfers to the original relation by its actual affine étale zero
chart. All relations and schemes are in arbitrary universe `u`.
