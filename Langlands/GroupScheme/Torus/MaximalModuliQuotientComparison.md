# Comparing supplied maximal-torus moduli with a normalizer quotient

This internal helper assumes a smooth affine group over an arbitrary base,
a supplied universal closed fibrewise maximal relative-torus family, and
a fixed closed fibrewise maximal relative torus. When a representative of
the full normalizer and an actual homogeneous quotient by it are supplied,
`normalizerQuotientComparison` descends the orbit map to the parameter
scheme. It recovers the original orbit after the quotient projection and
is a monomorphism on underlying schemes. The proof uses equality of the
all-test fibers, fpqc effectivity of the quotient projection, and the
published monomorphism theorem for a descended map with identical fibers.

`exists_etaleCover_maximalOrbit_lifts` proves that the orbit has sections
on an etale cover of the parameter scheme. Apply the published etale-local
conjugacy theorem to the fixed torus pulled to that scheme and its supplied
universal family. Transport conjugacy through the direct/iterated ambient
comparison and remove the corresponding source comparison. Each conjugator
then gives an actual group-valued parameter on the original base. The orbit
evaluation formula and evaluation injectivity prove its local section
identity.

`normalizerQuotientIso` turns the comparison into an isomorphism over the
original base. Compose each local orbit section with the quotient projection.
The comparison is monomorphic, so these local maps agree on all relations of
the etale cover. The cover is an effective epimorphic family, which glues them
to an actual inverse. The local section identities imply the first inverse
identity, and monicity implies the second. The compatibility with the base
map then promotes the isomorphism to `Over S`.

`quasiAffineOver_of_normalizerQuotient` transports quasi-affineness above
every affine open of the original base through the inverse comparison.

This module assumes the homogeneous quotient and its quasi-affineness when
used in the final transport theorem. It does not construct quotient
geometry, a maximal torus, or a universal parameter scheme.
