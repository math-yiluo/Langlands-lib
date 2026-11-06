# The actual number-field finite-level adelic Weil homeomorphism

This derived construction completes the finite-level point-space comparison
in Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
Example 4.2, printed page 10, for actual number fields K and L with their
original embedding. S is any finite set of original lower finite places.
The upper exceptional set is its full original preimage; all infinite
places occur in the existing full adelic levels on both sides.

`indexMap` sends a pair consisting of an original lower level coordinate
and an original upper place above it to the corresponding original upper
level coordinate. Infinite places remain infinite coordinates. At finite
places, `finitePlacesAbove_under` and
`mem_numberFieldExceptionalPreimage` verify that the upper place belongs
to the exceptional set exactly when the lower one does. Hence field factors
map to field factors and integer factors map to integer factors.

`indexInv` uses the original infinite-place restriction `comap` and the
original finite-prime restriction `under` to recover the lower coordinate.
The associated upper place lies over its restriction. The proof of
`indexEquiv` uses the original infinite-place `LiesOver.comap_eq` and
`finitePlacesAbove_under` to verify the inverse identities. It therefore
includes each original upper place exactly once, without an additional
place-system or fiber-decomposition hypothesis.

`factorPointHomeomorph` identifies the same original completed coefficient
ring and point topology before and after reindexing. In the two field cases,
algebra extensionality explicitly verifies that the upper level's
projection-induced coefficient algebra equals the coefficient action used
in the original local factor. After this equality is applied, the point
homeomorphism is the identity. The completed-integer case is definitionally
the identity. All point topologies are the independently constructed
`schemePointTopology` for the actual upper model.

`productPointHomeomorph` takes the product of these original factor
homeomorphisms and reindexes it with `indexEquiv`.
`productPointHomeomorph_apply` records the exact value at the upper
coordinate corresponding to any original pair.

Let Y be an actual upper S-integer model, locally of finite type,
quasi-compact and quasi-separated, with a specified relative immersion
into finite-dimensional projective space. `adelicLevelPointHomeomorph`
constructs the homeomorphism from actual lower adelic-level points of its
integral Weil model to actual upper adelic-level points of Y. Both sides
use their existing `numberFieldLevelModelPointTopology`.

The proof composes `NumberFieldSIntegerLevelWeil.levelPointHomeomorph`,
the product regrouping above, the original factorwise
`schemePointBaseChangeHomeomorph`, and the inverse of the proved actual
upper model coordinate homeomorphism. The upper model's compactness and
quasi-separatedness supply that last homeomorphism; no quasi-compactness
or finite-type assertion about the lower Weil scheme is assumed.

`adelicLevelPointHomeomorph_coordinates` identifies the original upper
level coordinate map of the output with the regrouped original local Weil
components followed by the original base-change point equivalences. Its
proof is the inverse identity for that actual upper coordinate
homeomorphism. Together with the previous module's exact component law,
this retains the original local counits and literal lower projections.

This unit treats finite adelic levels, including both real and complex
infinite completions. Compatibility as levels enlarge, the comparison to
the original generic schemes, and the final full adelic Weil
homeomorphism remain separate host obligations.
