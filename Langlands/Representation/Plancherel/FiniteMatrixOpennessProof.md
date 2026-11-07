# Finite matrix irreducibility is open

The theorem `Langlands.Plancherel.finiteMatrixIrreducibilityOpenness` proves the
published `FiniteMatrixIrreducibilityOpennessStatement`, with independent
universes for the parameter space, labels, and finite coordinate type. The
parameter space is arbitrary, the labels need not form a finite set or a group,
and continuity is required entry by entry. Irreducibility means the published
common invariant-subspace dichotomy; this convention includes dimension zero.

This is an internal linear-algebra prerequisite for the actual unramified
parabolic-induction argument. The proof uses the published Burnside engine
`Langlands.SandwichDimensionBound.action_surjective` and Mathlib's free algebra,
finite-dimensional linear independence, and matrix-to-endomorphism equivalence.
It does not use any representation-theoretic generic irreducibility statement.

The algebra-generation lemma lifts a finite basis through evaluation from a
free noncommutative algebra. Each lifted basis vector is a continuous function
of the generators. Linear independence of a finite family is open, and a
linearly independent family of the full dimension spans the entire algebra.
This proves openness of the full-algebra locus for a finite-dimensional normed
complex algebra.

For a nonzero finite-dimensional complex vector space, absence of proper common
invariant subspaces makes the action of the generated endomorphism algebra
simple. Burnside surjectivity then identifies this algebra with the full
endomorphism algebra. Conversely, a subspace invariant under the generators is
invariant under their algebra, by induction on algebra generation; the natural
module for the full endomorphism algebra is simple. These implications are
transported to matrices through `Matrix.toLinAlgEquiv'`. In dimension zero both
the invariant-subspace dichotomy and equality with the full matrix algebra hold
by subsingleton elimination.

Finally, entrywise continuity gives continuity into the matrix algebra, using
the operator norm topology. The algebra-generation openness lemma and the
matrix equivalence give the exact published conclusion.

This result alone supplies neither an irreducible parameter nor an
irreducibility criterion for an infinite-dimensional induced representation.
Applying it to actual compact-fixed families still requires continuity,
specialization, and uniform detection of representation subquotients.
