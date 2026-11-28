# Relative cocycle descent with local triviality

Given a natural cocycle on an fpqc cover over a number field, consider an
fpqc scalar extension of the base on which the cocycle becomes trivial.
`Cocycle.exists_locallyTrivial_of_baseChangePullback` puts the class on the
cover defined by that extension. If the original cocycle is locally trivial,
the new representative is also trivial on the full pullback cover to every
completion. Triviality on the new cover implies triviality on the original
cover.

The relative trivialization gives a cochain on the product of the two
covers. Twisting there makes the cocycle trivial on pairs with the same
image in the new cover. Effective fpqc descent gives the new cocycle and the
cohomology comparison on the product. The same comparison after every
completion extends the original local trivializations to the product.
The fpqc reflection of triviality gives both the local trivializations on
the new cover and the final implication on the original cover.

The kernel assertion over a number field extension can be tested on a
finite Galois refinement of the pullback cover. The transfer of local
triviality uses the maps between completions. Triviality on the field
refinement descends to the full pullback.

This is an internal application of `Cocycle.exists_isTrivialOver`,
`Cocycle.exists_refine_eq_of_comp_eq`, and fpqc reflection of coboundaries.
