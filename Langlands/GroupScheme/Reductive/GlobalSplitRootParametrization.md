# Actual global root parametrizations from free split root weights

This internal construction specializes the global dynamic root-group
parametrization to an actual reductive group with a supplied fibrewise maximal
coordinate torus, fibrewise reduced root datum and free actual root weights.
It is derived from the published root-group field-fibre and root-coordinate
interfaces; it introduces no new external source assertion.

A cocharacter generic in the root's coordinate kernel is chosen using the
pure integral-exponent separation theorem over an auxiliary lifted rational
field. The contracting cocharacter is the root's own exponent vector: its
pairing with that root is the positive sum of the squares of its coordinates.
This construction needs no field algebra over the base ring, so it also
applies when the base is the zero ring.

On every actual field fibre, the fibrewise root datum identifies the roots
annihilating the centralizing cocharacter with the chosen root and its negative.
The positive contracting pairing supplies the actual equivariant additive-group
fibre isomorphism. The global root-coordinate construction then gives an actual
root parametrization over the original ring, using the supplied free actual
root-weight trivialization.

The chosen family represents each actual root subgroup, has closed subgroup
inclusions and is torus-equivariant on every scheme test. All results retain
arbitrary commutative rings in universe u, without connectedness, reducedness,
localness or field assumptions on the base.

`exists_rootParametrization_of_free_weight` supplies each map.
`rootParametrizationsOfFreeWeights` chooses a family, and
`isRootParametrization_rootParametrizationsOfFreeWeights` proves its actual
root-subgroup representation and equivariance property for every root.
The family is the input used by the split Borel chart and vector-series
assembly; this module itself does not assert that final structural theorem.
