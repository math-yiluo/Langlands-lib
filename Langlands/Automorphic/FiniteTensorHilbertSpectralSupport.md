# Scalar spectral support of actual completed tensor slices

Author: Worker 2.

This is an internal construction and derivation from the published joint
eigenspaces, full projections, original corner actions and genuine smooth-model
fixed-space equivalence. No new identification with original literature is made.
Coefficients are complex; the field, carrier and operator-index universes remain
independent.

## Scalar tuples and their finiteness

For an arbitrary family `T : ι → Module.End ℂ A`,
`TensorHilbertHeckeAux.jointScalarSupport T` is the set of functions `c : ι → ℂ`
whose original joint eigenspace is not bottom.
`mem_jointScalarSupport_iff` identifies membership with the existence of an
actual nonzero vector satisfying every equation `T i x = c i • x`.
This is point support. It does not require scalar action on the whole space.

`jointScalarSupport_equiv` preserves this entire set under a supplied genuine
linear equivalence intertwining every original operator. The proof applies the
published nonzero-joint-eigenspace equivalence for each scalar tuple. The two
carrier universes can differ.

`jointScalarSupport_subset` puts every coordinate of an occurring scalar tuple
in the actual eigenvalue set of its coordinate operator, using the same nonzero
common eigenvector. For a finite index type and finite-dimensional `A`,
`finite_jointScalarSupport` proves the support finite. It uses pinned Mathlib's
`Module.End.finite_hasEigenvalue` from `Eigenspace.Minpoly`, which bounds the
eigenvalues by the roots of the minimal polynomial. `Set.Finite.pi` then gives
a finite set of possible tuples containing the support. Neither commutation,
normality nor simultaneous diagonalization is assumed. No dimension bound on
the number of tuples is claimed.

`jointScalarSupport_eq_singleton` assumes the existing `HasScalarSpectrum T c`,
including nontriviality of `A` and the equations on every vector. Any occurring
tuple equals `c` by cancellation on its nonzero common eigenvector. A nonzero
vector of `A` also proves that `c` occurs. Thus the support is exactly `{c}`.
The converse is not asserted: singleton point support alone need not give
whole-space scalar action.

## Original smooth models and corner projections

For a Borel topological group, a supplied Haar measure, compact open subgroup
and arbitrary family of corner elements, `cornerScalarSupport` uses the original
corner operators on all fixed vectors of an invariant subrepresentation.
`cornerScalarSupport_eq_model` identifies it with the support on the fixed
vectors of a supplied smooth model. The given representation equivalence must
target exactly the intersection of the invariant subrepresentation with the
ambient smooth subrepresentation. The proof uses `factorFixedEquiv` and
`cornerAction_factor`, preserving the original vectors and operators.

For a finite operator family, `finite_cornerScalarSupport` derives finiteness
from `IsAdmissible` of that same genuine model. It installs the model's actual
finite-dimensional open-subgroup fixed space and applies the preceding
coordinate finiteness theorem after the support comparison. It does not assume
smoothness of the whole Hilbert completion or finiteness of the ambient space.

For a complete complex inner-product space and a complete submodule carrying
continuous operators, `ambientJointProjection_eq_zero_iff` identifies vanishing
of the existing full-domain joint projection with the original joint eigenspace
being bottom. In the forward direction the projection fixes each original joint
eigenvector, forcing it to vanish. Conversely, the exact range formula makes
the projection's range bottom and therefore the operator zero.
`mem_jointScalarSupport_iff_ambientJointProjection` takes the negation of this
equivalence.

`mem_cornerScalarSupport_iff_fullJointProjection` specializes this criterion to
the original corner operators on a closed invariant subspace of a complete
complex inner-product space with a norm-preserving action. Closedness and the
published fixed-space completeness theorem supply the two completeness
instances. The continuous corner action forgets to the same algebraic action.
Thus point-support membership means precisely that the unchanged projection
on the entire invariant subspace is nonzero.

## Actual completed tensor slices

`FiniteTensorPresentation.hilbertSphericalScalarSupport` applies
`jointScalarSupport` to `sliceHilbertStandardHeckeOperator` on every spherical
fixed vector of the original closed completed tensor slice. It is a set of
scalar functions `Fin (r + 2) → ℂ` for rank `r + 1`, rather than a set of unordered
Satake parameter multisets. The operators retain the published mass-one
`sphericalHaar`, integral compact open subgroup, standard double cosets and
scalar normalization.

The presentation and invariant positive form are supplied genuine data.
The definition allows zero complementary tensors and needs no irreducibility
or admissibility assumption. The generic comparison and finiteness theorems
apply when a genuine smooth model and its admissibility are supplied; original
factor recovery through `factorHilbertSmoothEquiv` retains its explicit nonzero
tail and original-factor admissibility hypotheses. No additional concrete
comparison or finiteness wrapper is exported.

No existence of the presentation or positive form, nonempty support, spectral
decomposition, classification, parameter realization or automorphic occurrence
is asserted.
