# Cocycle vanishing under surjective scalar change

This internal algebraic helper extends `GroupoidCoactionScalarChange` and
`GroupoidCoactionIdealRestriction`. Rings have arbitrary universe `u` and
coefficient modules have independent arbitrary universe `v`.

`IsOneCocycle.scalarChange` sends a cocycle for the original ring relation to
a cocycle for a compatible surjective change of the scalar ring. The
original relation is assumed to be an actual `RingEtaleEquivalenceRelation`.
Its universal cocycle equation allows specialization at the new test
algebras even though they need not be flat over the original scalar ring.
The compatibility identities for tensor base change and coaction
composition then give the new cocycle equation. No flatness of the
surjective scalar map is assumed.

Scalar change also commutes with coboundaries. Consequently,
`oneCohomologyVanishes_of_scalarChange` reflects degree-one vanishing if
the scalar-change map on the coefficient tensor is injective.
`idealQuotient_oneCohomologyVanishes_of_idealRestriction` applies this
reflection to the previously constructed ideal restriction.

For any module annihilated by an ideal `I`, its coefficient tensor is
annihilated by the extension of `I`. Tensor right exactness therefore
makes reduction of the relation ring injective. The comparison of tensor
products over `B` and `B/I` is an equivalence, so changing both the
relation ring and tensor base remains injective. These are
`map_source_le_annihilator_tensor` and
`scalarChangeTensor_quotient_injective`.

`annihilatorRestriction` is the coaction on the quotient relation obtained
from any coefficient module already carrying a compatible `B/I` action.
It changes the relation ring and tensor base without changing the
underlying coefficient module.

Finally, `finiteAnnihilatorVanishing_of_quotient` installs the natural
`B/I` action on each finite module annihilated by `I`, transports its
coaction to the quotient relation, and reflects vanishing there. It
concludes the existing `FiniteAnnihilatorVanishing` predicate. It assumes
the finite-module vanishing theorem on the quotient relation; it does
not prove the support induction or the host acyclicity theorem.

All constructions are derived internally from the Library's universal
cocycle specialization, surjective scalar change, tensor right
exactness, and Mathlib's action of a quotient ring on an annihilated
module. No external theorem or affine-descent conclusion is assumed.
