# Orthogonal joint Hecke projections on full completed tensor slices

This is an internal construction from the existing actual closed tensor slice,
bounded corner action, ordinary joint eigenspace and Mathlib orthogonal
projection. It asserts no new identification with original literature.

For an algebraic complex representation whose group operators preserve the
ambient norm, `fixedVectors_isClosed` writes the fixed space of any subgroup
as an intersection of closed equalizers of bounded group operators with the
identity. Each group operator is continuous by its norm identity. No continuity
in the group variable or group topology is needed for this step.
`fullFixed_completeSpace` applies this result inside a closed invariant
subspace of a complete ambient normed space. Both the invariant subspace and
its full subgroup-fixed space are complete for their inherited ambient norms.

For any family of bounded operators on a complex Hilbert space,
`jointOrthogonalProjection` is Mathlib's `starProjection` onto the actual
intersection of ordinary eigenspaces for the prescribed scalars. The existing
closedness theorem gives completeness of that intersection, which supplies
the orthogonal projection. The projected vector satisfies every original
eigen-equation. A vector is fixed by the projection exactly when it satisfies
all those equations. The operator is idempotent and symmetric, its operator
norm is at most one, and it does not increase vector norms. Its range is exactly
the joint eigenspace, its kernel is the orthogonal complement, and the discarded
residual belongs to that orthogonal complement. These laws apply the
corresponding Mathlib projection laws to the actual closed joint submodule.

`cornerJointOrthogonalProjection` applies this construction to the existing
`cornerContinuousAction` on **all** subgroup-fixed vectors of a closed invariant
subspace. The ambient representation is required to preserve norms. The full
fixed space is proved complete; no finite-dimensionality, admissibility or
smoothness hypothesis is added. Its range is exactly the already defined
algebraic `cornerJointEigenspace`, and its fixed-vector criterion uses the
unchanged algebraic `cornerAction`. This follows from the definitionally
unchanged linear maps underlying the continuous action.

`sliceHilbertJointCornerProjection` specializes this actual construction to
`P.sliceHilbertRange` in `b.HilbertCompletion`. Closedness comes from
`P.isClosed_sliceHilbertRange`, and norm preservation comes from
`b.completedRepresentation_norm` at the original local inclusion. Thus the
carrier is the full fixed space of the actual completed tensor slice in the
supplied global completion. The Haar measure, compact open subgroup, corner
elements and scalars remain explicit and unchanged.

The coefficients are complex. Number-field, original factor, group, Hilbert
carrier and indexing universes are independent where applicable; the actual
tensor construction allows arbitrary rank and arbitrary complementary tensor,
including zero. A genuine presentation and invariant positive form remain
supplied inputs. No nonzero joint eigenspace, commuting Hecke family, spectral
decomposition, automorphic occurrence, positive-form existence or tensor
presentation existence is asserted.
