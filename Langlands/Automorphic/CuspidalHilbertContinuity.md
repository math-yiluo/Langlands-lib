# Joint continuity of the conditional actual adelic Hilbert action

`CuspidalAdelicHilbertContinuityStatement` retains the explicit
`CuspidalHilbertOrbitCoefficientStatement` premise, an arbitrary-universe number
field with compact `AdeleQuotient`, an actual cuspidal operator realization of
`GL_(r+1)`, a prescribed unitary central character, and a supplied full positive
form whose inner product is exactly the canonical determinant-band integral.
It asserts joint norm continuity, in the full actual adelic group and completed
vector together, of the previously constructed `adelicHilbertRepresentation` on
the same prescribed form completion. `cuspidalAdelicHilbertContinuity` proves the
statement. The generic Prop-valued predicate
`UnitaryEmbeddingFamily.JointlyContinuousRepresentation` means precisely
continuity of `(a,x) ↦ U(a)x` with the given group and Hilbert norm topologies.
It does not refer to operator-norm continuity of `a ↦ U(a)`.

The proof uses only continuity from the stronger retained coefficient premise.
For any vector of the full actual band `L²` space, the scalar pairing with the
infinite translate of each original vector is the prescribed smooth coefficient,
so it is continuous. Finite source orbits are locally constant because the
actual finite representation is smooth. The actual finite/infinite factorization
therefore makes each full adelic scalar pairing continuous: locally the finite
source vector is fixed and only its infinite parameter varies. No topology is
imposed on the original algebraic carrier for this argument.

For a map into a complex inner-product space with constant norm, continuous
scalar pairings imply norm continuity. The generic proof writes the norm of a
difference as the square root of the norm-squared inner-product identity. Each
supplied translated embedding is isometric, so this criterion gives continuous
orbits on the canonical dense original carrier. The uniform Lipschitz constant
one and Mathlib's dense-section continuity theorem then give joint continuity
of the target embedding family on all completed vectors. The identity isometry
reflects continuity back to the original source, by the exact target values of
the generic reconstructed action.

This is internal Hilbert-space analysis applied to the unchanged actual quotient,
measure, functions, embeddings and form completion. No new external theorem is
claimed. The coefficient premise is still unproved. Differentiable smooth-vector
and genuine generator comparisons, fixed-level derivative density, Whittaker
uniqueness and unconditional cuspidal operator multiplicity one remain outside
this result.
