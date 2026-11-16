# Nonempty opens in the full field fibres of the Chevalley closure

For a finite reduced root datum with finitely generated character lattice,
`fullFieldCellOpen` is the open image of the full negative-root, torus and
positive-root ordered product after base change to a field. The open is in
the full scheme fibre of the fixed integral closure. Its definition depends
on the integral data and the field-valued base point, before choosing a
field Chevalley group.

This is an internal consequence of `IntegralOpenCell` and `FieldCellImage`.
The integral ordered product is an open immersion, and open immersions
remain open after base change. To prove nonemptiness, take the test scheme
`Spec k`, with its specified map to the integral base. Choose zero in every
root parameter and the identity in the full coordinate torus, and combine
these points using the cartesian product. The pullback universal property
then gives a point of the base-changed parameter scheme from the zero prime
of the field. This construction includes empty root sets and retains all
central torus directions.

For every supplied field Chevalley group, `fieldOrderedCellFactor_comp`
identifies the pulled-back ordered product with its factorization through
the closed field embedding. Taking underlying points proves
`fullFieldCellOpen_subset`. Thus the same nonempty open is contained in each
such image. `exists_fullFieldOpen` combines this construction with the
existing existence of field Chevalley groups.

Finally, `integralExistence_of_smoothClosure` uses this unconditional
full-field open-image property in `NeutralExistence`'s conditional reduction.
It proves the unchanged integral-existence statement under the remaining
explicit hypothesis that every fixed integer closure is smooth.
This module does not prove that remaining hypothesis.
