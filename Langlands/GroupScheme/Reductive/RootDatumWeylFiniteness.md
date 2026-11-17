# Finiteness of the full Weyl groups of supplied fibrewise root data

This derived unit proves full integral Weyl-group finiteness for actual
supplied fibrewise coordinate root data over a nontrivial base ring. It does
not assume that the roots span the entire character lattice.

`IsRootDatumOf.weylGroupImageHom` maps the abstract Weyl group of an actual
field root datum into the actual normalizer image on the entire character
lattice. The existing abstract-Weyl-image containment supplies its image
certificate, and faithfulness of the full weight action makes it injective.
`finite_weylGroup_of_closed_split` applies the published finiteness of the
normalizer image of a closed split torus in an affine algebraic group.

`IsFibrewiseRootDatumOf.finite_weylGroup_of_field` specializes the actual
root datum to any supplied field-valued fibre. Reductivity and fibrewise
torus maximality give an actual closed split maximal torus in its affine
algebraic fibre. The field result gives finite realized Weyl group, and the
existing full root-datum equivalence transports that finiteness back to the
original coordinate datum, including its central lattice directions.

`finite_weylGroup` chooses a maximal ideal of a nontrivial commutative base
ring and uses its quotient field as that fibre. It requires no local,
noetherian or reducedness hypothesis. `finite_zeroReflectionSubgroup` then
applies the published inclusion of each zero-root reflection subgroup into
the full Weyl group. The nontrivial-ring premise is explicit; this unit does
not assert an existence of field fibres for the zero ring.

Provenance is the existing actual root-datum Weyl-image containment and
faithful weight action, the published finite actual normalizer-image theorem,
full coordinate field-realization equivalence, and maximal-ideal existence.
The abstract integral Weyl-group argument is the same as the published
`SplitPinning.finite_rootDatum_weylGroup`, exposed here for arbitrary supplied
actual root data and their field fibres without pinning hypotheses.
