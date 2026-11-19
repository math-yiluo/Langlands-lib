# The cuspidal class bound for finite general linear groups

`cuspidalClassCountBound` proves the published `CuspidalClassCountBoundStatement`
for every positive rank and both universe parameters. The proof compares
multisets of cuspidal classes with multisets of irreducible polynomial factors.

For a nontrivial additive character, the finite Gelfand–Graev representation
is induced from the entrywise character of the upper-unitriangular group. Its compatible
double cosets give the endomorphism dimension `Nat.card kˣ * Nat.card k ^ m`
in rank `m + 1`. The transpose criterion makes the endomorphism algebra
commutative, which gives multiplicity one for its irreducible constituents.
Cuspidal genericity and the product formula for Whittaker dimensions give
one generic constituent in each induction from cuspidal block factors.
Harish–Chandra support existence, disjointness, and invariance under reordering
then identify those constituents with the cuspidal multisets of total rank
`m + 1`. The classical Gelfand–Graev formulas are in Brundan–Dipper–Kleshchev
(2001), Theorem 2.5d, printed page 45.

On the polynomial side, unique factorization identifies the multisets of
total degree `m + 1` with the monic polynomials of that degree having nonzero
constant coefficient. Choosing the nonzero constant coefficient and the `m`
intermediate coefficients gives the same count. Both multiset types contain
only the empty multiset at weight zero.

For either set of labels, a multiset of weight `n` is a singleton of weight
`n` or uses only labels of smaller weight. The strong induction in
`WeightedMultiset.card_fiber_eq_of_card_eq` cancels the smaller-weight part,
giving equal cardinalities of the weight-`n` fibers. For `n > 0` the cuspidal
fiber is equivalent to the finite-dimensional cuspidal model classes, and the
polynomial fiber is equivalent to the published label subtype. The model
equivalence transfers the count to the cuspidal classes in the statement's
carrier universe. The equality of finite cardinalities gives the requested
extended-natural inequality.
