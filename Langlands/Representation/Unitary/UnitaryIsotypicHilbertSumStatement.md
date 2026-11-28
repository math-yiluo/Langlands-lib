# Isotypic components of a unitary Hilbert sum

Let a group act by inner-product-preserving bounded linear operators on a
complex Hilbert space. Suppose the space is the internal Hilbert sum of a set
of nonzero closed invariant subspaces with topologically irreducible
restricted actions. Suppose also that only finitely many of these summands
are unitarily equivalent to any given summand. Two restricted actions are
unitarily equivalent when a surjective complex-linear isometry intertwines
their actions.

`UnitaryIsotypicHilbertSumStatement` says that the algebraic sums within the
unitary equivalence classes are closed, invariant, and form an internal
Hilbert sum. The orthogonal projection onto each such sum is the finite sum
of the projections onto its summands. For a representative of a class, the
component is the supremum of all nonzero irreducible closed invariant
subspaces unitarily equivalent to that representative, including subspaces
outside the given Hilbert sum's index set. This equality characterizes the
subspace independently of the chosen decomposition.

Getz–Hahn, *An Introduction to Automorphic Representations*
(`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`),
Corollary 9.1.3 and (9.5), printed p. 241 (PDF p. 253), describe this grouping
for the cuspidal Hilbert sum. The proof of Theorem 9.7.3 at (9.40), printed
p. 266 (PDF p. 278), uses the finite sum of equivalent irreducibles within an
isotypic component. The proposition isolates the representation-theoretic
step after discreteness and finite multiplicity. The projection identity
follows from orthogonality within a finite class. The intrinsic description
uses Schur's lemma on the projection of an arbitrary irreducible subspace
onto each original summand.
