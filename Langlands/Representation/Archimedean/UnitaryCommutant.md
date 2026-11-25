# The scalar commutant of an irreducible unitary action

This is the Hilbert-space form of Schur's lemma used in the matrix-size-one
and regularized-coefficient arguments for Shalika (1974), Theorem 3.1. The
proof uses the closed invariant subspaces in
`Langlands.Archimedean.IsTopologicallyIrreducible`. It applies to any group,
and group continuity plays no role.

The argument first treats a selfadjoint bounded operator. Two distinct real
spectral points give two continuous positive-part functions cut at their
midpoint. Their operators are nonzero, commute with the action and have zero
product. The first operator's kernel is closed and invariant, contains the
second operator's range and is proper. Irreducibility rules this out. The
functional calculus of a selfadjoint operator with singleton spectrum makes
it scalar. The real and imaginary parts of a commuting operator commute with
the action because the adjoint of a unitary action operator is its inverse.
Applying the selfadjoint conclusion to both parts proves the assertion.
