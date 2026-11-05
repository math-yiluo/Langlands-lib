# Finite-rank compact projections from genuine admissible smooth models

Author: Worker 2.

This internal derivation uses the existing full-domain joint projections,
their composition formula and the genuine fixed-space equivalence with a
supplied smooth model. It asserts no new identification with original literature.

For a finite-dimensional complex submodule `K`, the ambient joint eigenspace
is finite dimensional because it lies in `K`. Monotonicity bounds its dimension
by that of `K`. In a complete ambient inner product space the existing exact
range identity proves the same finiteness and dimension bound for the actual
range of `ambientJointProjection`.

`ambientJointProjection_isCompact` uses its proved composition formula:
project to `K`, apply the original joint projection there, and include into the
ambient space. Finite-dimensional complex normed spaces are locally compact.
Mathlib's compact-operator composition laws therefore prove compactness of
this precise continuous endomorphism. No commutativity or nonzero eigenspace
is assumed; the operator index has an independent universe.

For a closed invariant subspace of a complete norm-preserving representation,
`fullFixedOrthogonalProjection_isCompact` proves compactness of the existing
orthogonal projection onto all subgroup-fixed vectors from their explicit
finite dimensionality. The group needs no topology for this assertion.
With a topological group, Borel Haar measure and compact open subgroup,
the full corner joint projection has finite-dimensional range, dimension
bounded by the entire fixed space, and is compact under the same finite
dimensionality hypothesis. The operators, Haar measure, vectors and inherited
norms remain the original ones.

The `factorCornerFullJointProjection` results obtain this hypothesis from
`IsAdmissible` of a supplied genuine smooth model and an actual representation
equivalence onto the smooth intersection of the invariant subspace. The
existing `factorFixedEquiv` transports the model's finite-dimensional fixed
space onto the full invariant-subspace fixed space. Its dimension equality
also bounds the projection range by the original model's fixed dimension.
No topology on the model carrier or smoothness of the full completed
representation is assumed. Model and ambient carrier universes are independent.
`factorFullFixedOrthogonalProjection_isCompact` uses the same equivalence and
admissibility to prove compactness of the full fixed-subspace projection.

`sliceHilbertFullFixedProjection` supplies the actual closed tensor slice in
the global positive-form Hilbert completion, its proved closedness, and the
original norm-preserving completed action at the local insertion. It is a
continuous endomorphism of the entire slice, projecting onto every vector
fixed by the specified subgroup. Its construction allows every natural rank
and zero complementary tensors, and needs neither admissibility nor
irreducibility. The existing generic exact range and fixed-vector laws apply
to these same inputs.

The generic smooth-model compactness, finite-range and dimension results can
be used with these actual inputs and the published
`factorHilbertSmoothEquiv`. That equivalence retains the explicit nonzero tail
and original-factor admissibility; its target is the actual smooth intersection
in the global completion topology. No concrete compactness specialization is
exported here. Field and original-factor universes are independent;
coefficients are complex.

All constructions are conditional on the displayed data. They assert no
existence of a smooth model, invariant positive form, tensor presentation,
nonzero eigenspace, prescribed spectrum, decomposition or automorphic
occurrence.
