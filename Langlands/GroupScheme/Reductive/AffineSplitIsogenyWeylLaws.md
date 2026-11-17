# Positive Weyl-action laws for the actual powered family

This internal derived unit proves braid, simple-root, A2 and B2 map
identities for the actual powered Weyl family of a root-datum isogeny.
It uses the original characteristic condition and genuine normalized
target data over a commutative local ring, with affine ambient target.
The braid construction also requires the target torus inclusion to be closed.

The weighted Cartan identities imply equality of the two Cartan products,
so the braid lengths agree even when root lengths are exchanged. Actual
powered Weyl products equal the reindexed genuine target Weyl products.
The published genuine target braid theorem, using the published
opposite-partner uniqueness theorem, therefore gives the required
conjugations on every additive-line map.

Root powers commute with minus-one scaling. More generally, scaling the
input by a scalar scales its genuine target coordinate by the scalar's
root-factor power. These exact map identities transport the A2 sign and
the B2 sign when lengths are preserved.

In the exchanged B2 case the root-factor ratio forces characteristic two.
The target conjugated long-root map is fixed by the other long-root Weyl
product: the target B2 coefficient classification excludes both mixed
cones, and its Cartan entry is zero. The published fixed-conjugation
theorem gives this genuine target identity. Minus one equals one in the
original coefficient ring, yielding the required source sign before
powering. No parametrization property of powered maps is assumed.

The simple-root opposite action follows from the genuine target simple
action, exact word transport and equality of opposite root factors.
`PoweredWeylTransportRelations` records these four identities, and
`poweredWeylTransportRelations` proves the bundle from the stated genuine
target hypotheses and the original characteristic condition.
Square and no-cone fixed actions are in `AffineSplitIsogenyWeylActions`;
the arbitrary-unit negative action and full U1 assembly remain separate.
