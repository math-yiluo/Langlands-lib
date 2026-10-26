# Composed-to-flattened normalized induction

Authors: Worker 578 and Worker 125 (the canonical Levi-map comparison adapted
from the published generic proof).

This file proves the exact closed proposition
`Langlands.Parabolic.ComposedFlattenedInductionStatement.{uF,uV}` as
`Langlands.Parabolic.composedFlattenedInduction`.

The proof specializes the published
`Langlands.Parabolic.refinementCoordinatesNormalization` to the ordinary
shape `B.flatten S`, the outer shape `B`, and refinement `S`. Its block-label
equivalence is `B.flattenBlockEquiv S`. Its size equalities are the inverses
of `B.flatten_size_flattenBlockEquiv S`, and its coordinate hypothesis is
exactly `B.index_index_eq_flatten S`. No coordinate or normalization premise
is added to the final theorem.

The helper
`Langlands.GeneralLinear.BlockShape.leviRefinementEquiv_flatten` identifies
the generic actual Levi map at these canonical coordinates with
`Geometric.flattenedLeviEquiv`. Apply the inverse of `refinedLeviEquiv`
to compare the nested Levi products, then compare each inner matrix using
`nestedLeviEquiv_apply` and `flattenedLeviProductEquiv_apply`. Both reindex
the same flattened matrix by the same size equality.

Apply the generic induction clause to the ordinary Levi representation
`σ.comp (flattenedLeviEquiv F.Carrier B S).toMonoidHom`. Its composed
input is this representation pulled back by the inverse generic Levi map.
The helper identifies that map with `flattenedLeviEquiv`, so forward and
inverse coordinates cancel. Extensional equality of representations gives
exactly `σ`, not merely an isomorphic representation. Rewriting this
equality in the generic existential statement produces the required
equivariant complex-linear equivalence and retains both pointwise evaluation
formulas, for the forward map and its inverse.

The full determinant-character calculation, equality of the canonical
positive half characters, actual parabolic/projection compatibility and
comparison of smooth induced functions are supplied by the imported generic
normalization proof. This specialization repeats none of those arguments.
The resulting maps preserve every ambient function value. The imported
construction retains the uniform open right stabilizer and intertwines
right translation.

This is an internal specialization of published Library results. The field
and value universes remain independent. The original representation is
arbitrary, without a smoothness or finiteness premise, and the proof includes
rank zero and empty block families. It proves the direct composed-to-flat
comparison, with no claim about nested induction or Haar scaling.
