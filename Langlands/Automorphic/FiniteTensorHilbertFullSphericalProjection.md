# Canonical spherical projections on entire completed tensor slices

Author: Worker 2.

This internal construction uses the existing actual full joint projection,
canonical spherical operators and scalar-spectrum predicate. No new
identification with original literature is asserted.

For continuous operators on a complex submodule `K` of a complex inner
product space, `ambientJointEigenspace_eq_submodule_iff`
characterizes equality of the included ordinary joint eigenspace with `K`
by all the original scalar equations. The membership criterion identifies
the same subtype vector in the forward direction; the reverse direction
uses the two submodule inclusions.
When `K` and the ambient space are complete,
`ambientJointProjection_eq_starProjection_iff` characterizes equality of
their orthogonal projections by these same equations. In the forward
direction equality of ranges gives equality of the submodules. In the
reverse direction the full composition formula and identity criterion on
`K` reduce the joint projection to `K.starProjection`.
`hasScalarSpectrum_iff_ambientJointProjection` retains nontriviality of `K`
as a separate conjunct. This includes the possible zero submodule.

For a closed invariant subspace `S` in a complete norm-preserving complex
representation, `fullFixedOrthogonalProjection` constructs the orthogonal
projection on all of `S` onto all its subgroup-fixed vectors. The existing
closedness and completeness proofs supply the inherited complete spaces;
Mathlib's `starProjection` supplies the map. Its range is exactly the full
fixed submodule and its fixed vectors are exactly the subgroup-fixed ones.
The group need have no topology for this construction.

For the existing Haar measure, compact open subgroup, corner elements and
scalars, `cornerFullJointProjection_eq_fixedProjection_iff` applies the
generic criterion to the complete fixed submodule. Forgetting continuity
recovers the unchanged algebraic corner operators.
`hasScalarSpectrum_iff_cornerFullJointProjection` retains nontriviality
and equality with that full fixed-subspace orthogonal projection.

For a p-adic field with the canonical GL topology,
`sphericalFullJointProjection` uses exactly `Unramified.sphericalHaar`,
`sphericalOpenSubgroup`, `standardHeckeElement` and `standardHeckeScalar`.
Their existing mass-one normalization on the integral subgroup, all
standard diagonal indices and residue-cardinality square-root scalar
normalization remain unchanged. Its domain and codomain are the whole
closed invariant subspace `S`. Its range is the included original
algebraic joint eigenspace. Restriction to all spherical fixed vectors
recovers the previous `sphericalJointProjection` with the same vectors
and norm. The whole spherical scalar-spectrum criterion is nontriviality
of the full spherical fixed space together with equality of this map and
the orthogonal projection onto that space.

`sliceHilbertFullSphericalProjection` supplies the actual full closed tensor
slice in the global positive-form Hilbert completion, its proved closedness
and the original completed action restricted along the actual local
inclusion. Its domain includes every vector of the completed slice. The
generic canonical range, restriction and whole-spectrum laws apply to
these identical inputs. The inherited full joint projection laws provide
idempotency, symmetry, norm bounds and orthogonal residual and kernel.

The number-field and original-factor universes are independent. Coefficients
are complex, ranks are every positive natural number `r + 1`, and complementary
tensors may be zero. The generic operator index also has an independent
universe. No irreducibility or admissibility assumption is used. The genuine
tensor presentation and invariant positive form are supplied. The construction
asserts no existence of those inputs, nonzero eigenspace, prescribed spectral
occurrence, spectral decomposition or automorphic existence.
