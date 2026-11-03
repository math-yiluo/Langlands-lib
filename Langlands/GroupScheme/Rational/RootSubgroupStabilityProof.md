# Torus stability of intrinsic relative root subgroup functors

This internal, derived unit proves torus stability directly for the actual
relative-root functor from `RootSubgroup`. It works over every base scheme and
for every character, without assuming a root condition, splitness, a field or
representability.

`conjugateExtension` conjugates an actual affine-line extension by the pullback
of a fixed torus point. Commutativity of the torus makes the orbit equivariant,
so this construction extends the conjugated orbit through the same character.
Its value at zero is the conjugate of the original zero value. The identity
value is therefore preserved, proving `subgroup_isStable` on every test scheme.

The proof uses the published point-action naturality, multiplication laws and
Cartesian product identities. Its provenance is a direct internal consequence
of those constructions; no additional literature assertion is used. This
establishes the stability clause needed by
`RootSubgroupRealizationStatement`; representability, smoothness, connectedness,
unipotence, splitness and the Lie-image comparison remain separate obligations.

Author: Worker 1285.
