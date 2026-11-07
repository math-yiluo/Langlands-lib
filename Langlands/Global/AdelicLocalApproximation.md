# Approximation away from one actual adelic coordinate

This internal arithmetic input is derived from the published compact fundamental
set of the actual adeles and the finite-cover lemma
`exists_ne_zero_mul_mem_of_compact_section`. No global duality result is assumed.

The maps `HeckeFunctionalEquation.finiteAdditiveInclusion` and
`HeckeFunctionalEquation.infiniteAdditiveInclusion` from
`AdelicCoordinateInclusions` insert an element at the named
completion and zero at all other places. At a finite place this uses the actual
restricted product: the family is integral away from its single possible
exception. Projection back onto the named completion is a left inverse, and
multiplication of a single-coordinate adele is multiplication at that coordinate.

For each place, `finite_small` or `infinite_small` states that every adelic
neighborhood of zero contains `diagonal K k * (1-e)` for a nonzero field element
`k`, where `e` is the single-coordinate adele with value one. The completion is an
infinite Hausdorff topological field, so it cannot be compact. Apply the generic
finite-cover lemma to its single-coordinate section, which multiplication by
`1-e` annihilates, and to the actual compact representatives modulo `K`.

Finally, `exists_local_factor` takes any nonzero adele `a`. Some actual coordinate
`a_v` is nonzero. Take `e` equal to one at that coordinate and zero elsewhere,
and take `z` equal to `a_v` inverse at that coordinate and zero elsewhere. Then
`e = a*z`, and the corresponding small-element lemma gives the full quantified
neighborhood conclusion. This construction treats finite and infinite places
separately and preserves the actual completion topologies.
