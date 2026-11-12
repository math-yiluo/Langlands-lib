# Fixed-model number-field stages and original local Weil factors

This internal construction compares each arithmetic stage of a fixed
number-field Weil model with the product of all its original upper local
factor points. Infinite places and completed valuation rings are included.

Let `L/K` be an extension of number fields, `S` a finite set of finite
places of `K`, and `T` an enlarged finite support containing `S`. The upper
coefficient ring is the ring of integers of `L` outside the full preimage
of `S`. Let `X` over that ring be quasi-separated and of finite type, and
assume explicitly that its Weil restriction `W` to the S-integers of `K`
is algebraic. The local comparisons retain this algebraicity witness.
For the stage construction also assume that `W` is separated and of
finite type. These latter conditions supply its stage coordinate bijection.

`upperField` associates the original upper completed field to each upper
factor over each lower `T`-level coordinate. `upperFieldAlgHom` is the
identity for a field factor and the original inclusion for a completed
valuation ring. The coefficient actions on these fields are the original
ones from the fixed upper S-integers.

The field instances use the independently normalized completion norms.
The actual completion embeddings give continuous scalar multiplication;
finite dimensionality and completeness give the module topology.
`lowerField_henselian` and `upperField_henselian` apply the published
complete-local-field results to these norms.

`fieldTensorData` packages the original completed-field tensor comparison
with the fixed-base coefficient action. Equality of the algebra maps
identifies that action with the original S-integer action on the completion,
so the published finite or infinite tensor equivalence applies. Its second
component retains the original upper coefficient maps.

`fieldPointMap_isHomeomorph` applies the finite-type tensor field
comparison. The proof handles the three kinds of coordinates separately,
so each normed-field instance reduces to its original completion structure.
`factorPointHomeomorph` then applies the integral-to-field tensor comparison
at every coordinate, including those that are already fields. Its lower
tensor equivalence is exactly `NumberFieldSIntegerFixedLevelWeil.tensorEquiv`;
its upper row is `fieldTensorData`. The original coefficient square commutes
by the definitions of the completion maps and integral inclusions. This gives
the original lower Weil factor topology and the product of the original upper
factor topologies. The component formula is exactly
`completedTensorSpaceWeilRestrictionPointMap` for the fixed-level tensor.

`levelPointHomeomorph` composes the published fixed-base stage coordinate
homeomorphism with the product of `factorPointHomeomorph`, then writes the
nested product as the product over pairs of lower coordinates and upper
places above them. Both directions of this last reindexing are continuous
by coordinate evaluation. `levelPointHomeomorph_component` identifies each
forward component with the original fixed-level tensor Weil map after
coefficient change along `NumberFieldSIntegerFixedLevelWeil.levelFactorAlgHom`,
the original enlarged-level projection. It follows from the two component
formulas and the definition of that projection.

The provenance is internal composition of the actual arithmetic tensor
decompositions, original complete-local-field topology results, the integral
comparison, and the fixed-base stage coordinates. No scheme, smoothness or
projectivity assumption is imposed on `X`. This unit neither regroups the
upper factors into their own arithmetic stage nor proves the final adelic
homeomorphism; those assembly steps remain separate.
