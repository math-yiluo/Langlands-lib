# Canonical spherical operators on full completed tensor slices

This internal construction specializes the published full fixed-space corner
action to the existing canonical p-adic field, its mass-one spherical Haar
measure, its integral open compact subgroup, and its standard diagonal
double-coset elements. The presentation and positive form are genuine supplied
data. No new original-literature identification is asserted.

The topology comparison uses `localGL_topology_eq`. The generic
`TensorPadicAux.smoothInfTopologyEquiv` substitutes this equality and uses the
identity representation equivalence. Its forward and inverse value laws preserve the ambient vector.
`isSmoothOfTopologyEq` transports smoothness using that same equality.
The actual slice comparison does not require a nonzero complementary tensor,
admissibility or irreducibility.

`SliceHilbertSphericalVectors` is the fixed submodule of the full invariant
closed slice inside the original global Hilbert completion.
`sliceHilbertSphericalAction` uses the canonical normalized spherical corner,
and `sliceHilbertSphericalContinuousAction` uses the same operators with their
proved bounds. The ambient completed action preserves the inherited Hilbert
norm, as supplied by `completedRepresentation_norm`.
`sliceHilbertSphericalFixedEquiv` identifies all fixed vectors of the intrinsic
smooth slice with those of the full closed slice.

The standard operators use the existing `standardHeckeElement`, including
indices zero through the positive rank. The published generic unital and
forgetful corner laws apply to these same operators. The corresponding
eigenspace is the
actual intersection of ordinary eigenspaces for `standardHeckeScalar`, with
the inherited residue-cardinality square-root normalization.

This construction uses complex coefficients and independent number-field and
factor universes. Its positive rank is `r + 1` for arbitrary natural `r`.
It does not construct a global automorphic occurrence, a positive form, a tensor
presentation, a spectral decomposition or an eigenvalue system.
