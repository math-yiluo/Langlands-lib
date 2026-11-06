# Joint continuity on the original full AE cuspidal L2 space

This internal adapter restricts the existing canonical
`haarQuotientL2JointRightAction` to the unchanged
`fullAEL2CuspidalSubmodule`. Its carrier is precisely the original full
almost-everywhere cusp locus, with separate absolute convergence and
vanishing for every actual proper rational parabolic. The subgroup,
quotient measure, L2 null classes and right action are unchanged.

`fullAEL2CuspidalJointRightAction` is continuous jointly in the actual
adelic group element and cusp vector for the topology inherited from
the original quotient L2 space. Its evaluation is definitionally the
original restricted representation `fullAEL2CuspidalRightAction`.
Forgetting the cusp subtype recovers the original canonical joint
action exactly. Fixing a cusp vector produces the continuous
`fullAEL2CuspidalOrbitMap`.

The proof composes the ambient joint continuous map with the product
of the identity on the actual adelic group and the subtype inclusion
on the original cusp space. The previously constructed full
subrepresentation supplies membership of every value. Continuity
into a subtype then proves continuity in the inherited topology.
Neither closedness nor completeness is used.

The arbitrary number field, actual affine locally finite-type group,
connected reductivity and structural `ParabolicDynamicStatement`,
supplied central split torus, injective finite-index character
restriction, finite splitting and right invariance of norm-one Haar
remain explicit. No finite volume assumption is introduced.

Provenance is internal: this is a topological restriction of the
original full-AE subrepresentation and canonical quotient joint action,
using pinned Mathlib's continuity API for products and subtypes.
It proves no smooth or continuous-function density, spectral
decomposition or trace assertion.

The imported full-AE construction and canonical quotient continuity adapter
are published Library dependencies. This pair adds only their topological
restriction to the existing original cusp subtype.
