# Joint Hecke projections defined on entire completed tensor slices

This is an internal construction from the existing actual joint eigenspaces,
bounded corner actions, closed fixed spaces and Mathlib orthogonal projections.
No new identification with original literature is asserted.

For a complex submodule `K` of an inner product space `H`,
`ambientJointEigenspace` maps the ordinary joint eigenspace of the specified
continuous operators on `K` through the inherited subtype inclusion into `H`.
Membership means existence of that same vector in `K` with every prescribed
eigen-equation. Its image lies in `K` and is closed whenever `K` is closed:
the joint eigenspace is closed in `K`, whose inclusion is a closed map.

The projection construction takes complete `H` and complete `K`, with the
inherited norm on `K`. In particular it applies to every closed submodule of a
complete `H`, using its proved subtype completeness. Completeness of `K`
implies its closedness, so the image joint eigenspace is closed and complete.
`ambientJointProjection` is its actual continuous orthogonal projection,
constructed by `Submodule.starProjection`. Its range is exactly this image,
and its fixed-vector criterion is precisely the membership criterion above.

The subtype inclusion is a linear isometry. Mathlib's
`LinearIsometry.map_starProjection` proves that restriction to `K` recovers the
previous `jointOrthogonalProjection`, with the same vectors and norm. The nested
subspace absorption law `Submodule.starProjection_comp_starProjection_of_le`
proves the full formula: first apply `K.orthogonalProjectionOnto`, then the
original joint projection, then the same subtype inclusion.

Idempotency, complex inner product symmetry, operator norm at most one,
norm-nonincreasing application, orthogonal-complement kernel and orthogonal
residual follow from the corresponding Mathlib laws for this exact closed
submodule. The joint subspace may be zero. No commuting family or nonzero
eigenvector is assumed, and the operator-family index has an independent universe.

For a closed invariant subspace `S` of a complete complex inner product space
with a norm-preserving group representation, `cornerFullJointEigenspace` includes
the existing algebraic corner joint eigenspace into the whole space `S` through
its subgroup-fixed submodule. `cornerFullJointProjection` is a continuous
endomorphism of all of `S`. It uses exactly the existing `cornerContinuousAction`
for the supplied Haar measure, compact open subgroup, corner elements and
scalars. Its range equals `cornerFullJointEigenspace`; its fixed-vector criterion
requires the original algebraic corner eigen-equations and the same fixed-vector
inclusion. Restricting it to all subgroup-fixed vectors gives exactly the existing
`cornerJointOrthogonalProjection`. Idempotency and the operator norm bound are
also specialized explicitly. The other generic projection laws remain applicable.

`sliceHilbertFullJointCornerProjection` specializes this construction to the
actual `P.sliceHilbertRange b v y`. This is the full closed completed slice in
`b.HilbertCompletion`, with the inherited global norm. Its ambient group action
is the original completed global representation restricted along the local
inclusion. The constructor supplies `isClosed_sliceHilbertRange` and
`completedRepresentation_norm` at that same inclusion. Thus it acts on every
vector in the completed slice, including vectors outside its subgroup-fixed
subspace; its restriction to the fixed space agrees with the earlier projection
by the generic corner restriction law. The generic corner range, fixed-vector,
idempotency and norm laws apply to these same actual inputs.

Coefficients are complex; the number-field, original-factor and operator-index
universes are independent. Every natural rank and zero complementary tensors are
allowed. The genuine tensor presentation and invariant positive form are supplied
inputs. Their existence, original-factor recovery, prescribed spectral occurrence,
nonzero eigenspaces, spectral decomposition and automorphic existence are not
asserted. No factor admissibility or irreducibility premise is used.
