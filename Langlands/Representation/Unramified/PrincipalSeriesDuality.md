# Smooth duality of actual unramified principal series

This internal construction specializes the published normalized product duality
to the Library's actual unramified upper-Borel principal series. It has no
ordering, irreducibility, distinctness or unitarity hypothesis on the tuple.

`character_inv` proves that inverting a uniformizer value inverts the associated
actual unramified character, by evaluation on units and the integer-power
formula. `scalarCharacterSmoothDualEquiv` identifies the smooth dual of the
scalar GL1 character model with its inverse-character model. The algebraic-dual
equivalence is evaluation at one. Smoothness of the inverse character line
makes that entire algebraic dual smooth, so the smooth-dual inclusion is an
equivalence.

`principalSeriesOfTupleSmoothDualEquiv` constructs an actual representation
equivalence from the smooth contragredient of `principalSeriesOfTuple F z` to
`principalSeriesOfTuple F (fun i => (z i)⁻¹)`. Every scalar inducing character is
admissible, as follows by transport from the published lifted rank-one
supercuspidal character object. The normalized product duality therefore applies.
Pointwise smooth-dual character equivalences, the normalized induction
congruence and `character_inv` identify its target with the exact inverse-tuple
principal series. The field universe is arbitrary.
