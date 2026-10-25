# Cyclic Herbrand quotient invariance for full invariant real lattices

This module proves the published proposition
`Langlands.GroupTheory.CyclicLatticeHerbrandInvariance.{v,w}` with independent
universes for the group and the ambient real vector space. It is an adapter to
`Langlands.Cohomology.Herbrand.hasHerbrandQuotient_iff_of_bases`, which already
implements the lattice comparison in Milne, *Class Field Theory*, VII Lemma 3.5.

For an injective additive embedding whose range is the integer span of a real
basis, the private helper identifies its domain with that span by an integer
linear equivalence. The real basis is integer-linearly independent by restriction
of scalars. `Module.Basis.span` makes it an integer basis of its span; transporting
this basis back gives an integer basis whose image is the original real basis.

The closing proof applies this construction to both embeddings. Finite
dimensionality makes the first real basis's index type finite. The second real
basis and its corresponding integer basis are reindexed to that same type using
`Module.Basis.indexEquiv`. The given equivariance identities then satisfy the
hypotheses of `hasHerbrandQuotient_iff_of_bases` for the real linear maps underlying
the action. Applying the comparison to
`hasHerbrandQuotient_of_finite_cohomology M` proves that the first and second
cohomology groups of `N` are finite and gives the rational Herbrand quotient
identity. The cardinality of the finite, nonempty group `H¹(G,M)` is nonzero, so
clearing its denominator yields the required equality of natural-number products.

The imported lattice comparison supplies scalar descent and finite-index
invariance. The adapter needs no topology on the real vector space and no
nontriviality hypothesis on the group or the vector space. The statement and all
its imported definitions are unchanged.
