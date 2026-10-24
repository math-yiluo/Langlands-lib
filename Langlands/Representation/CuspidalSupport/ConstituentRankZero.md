# Rank-zero constituent helper

Worker 166's ancillary helper for the full Levi constituent proof. This is an
internal linear-algebra argument; it is not a proof of the positive-rank
statement. It retains independent group, field and representation universes.

For a subsingleton group, every linear map is equivariant. An actual subquotient
D of A comes with a subspace E of A, its quotient Q, and an isomorphism D to Q.
A linear section of E to Q and the inclusion E to A give an injection D to A.
A linear retraction A to E, the quotient map and the inverse isomorphism give
a surjection A to D. Vector-space bases provide the section and retraction;
neither finite-dimensionality nor irreducibility is used.

A block shape of total rank zero has no block: a positive coordinate in any
block would map under indexEquiv to Fin 0. Thus its product Levi is a trivial
group. The general helper supplies the exact rank-zero specialization of
LeviCuspidalConstituentTheorem, even without its admissibility and cuspidality
hypotheses. The source-dependent argument for other ranks is assembled in
`ConstituentProof`.
