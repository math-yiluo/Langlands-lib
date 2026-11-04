# Irreducible closed chains on open charts

This is a derived topological prerequisite for the chart arguments
needed for the pure-dimensional fibre clause of Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp. 5–6, Theorem 3.4(2). The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The topological result is not a separately numbered assertion of Conrad.

`restrictIrreducibleClosedSeries U p hne` constructs an actual strict
chain of closed irreducible subsets of the open subspace U from such
a chain p in X, when U meets the smallest member of p. Its members
are the preimages under the subtype inclusion, and its length is the
original length. Every member of p meets U because it contains the
smallest member. The implementation uses Mathlib's order isomorphism
between irreducible closed subsets of U and irreducible closed subsets
of X meeting U. This also proves strictness: closure in X recovers
each member from its nonempty open intersection.

For any family of opens covering an arbitrary topological space X,
`topologicalKrullDim_eq_iSup_openCover` proves that the dimension of X
is the supremum of their dimensions. For the upper bound, a strict
finite chain has a point in its smallest member; choose an open of
the cover containing that point and restrict the chain without
changing its length. The reverse bound uses the dimension inequality
for subspaces.

No separation, sobriety, Noetherian, quasi-compactness, or
finite-dimensionality assumption is imposed. The cover index and
space occupy independent universes. The empty space and empty cover
are allowed when the covering condition holds, with the supremum
then equal to negative infinity. This result concerns total
topological dimension; it does not assert constancy of dimension
on a nonempty open of an irreducible space or componentwise pure
dimension locality for general schemes.
