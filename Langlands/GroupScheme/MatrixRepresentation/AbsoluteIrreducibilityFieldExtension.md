# Absolute irreducibility from scalar self-intertwiners

This module proves part (b) of Milne, *Algebraic Groups* (2017),
Proposition 4.19, pp. 90–91 (`milne-2017-algebraic-groups`): an irreducible
representation whose actual self-intertwiners are all scalar stays irreducible
after every extension field in the base universe. The result applies to arbitrary
affine group schemes over fields; no finite-type or reducedness hypothesis is
needed for this part. The predicate `IsAbsolutelyIrreducible` records precisely
that field-extension property, using the Library's actual matrix base change.

The implementation uses the preceding internal operator-algebra reductions.
`AffineOperatorDensity` applies Jacobson density to show that the original
operator algebra is full. `AffineCoefficientBaseChange` shows that every actual
stable subspace after extension is preserved by every extended original operator.
If such a subspace is nonzero, choose a vector with a nonzero coordinate.
Original elementary matrices produce that coordinate times each new coordinate
basis vector. Scaling and summing inside the new-field subspace shows that it is
full. Irreducibility of the original representation ensures a nonempty coordinate
type and hence a nonzero extended coordinate space.

The main reusable theorem is
`MatrixRepresentation.IsIrreducible.baseChange_of_scalar_intertwiners`.
All stability and intertwining predicates retain arbitrary affine test algebras,
including nonreduced algebras. This module proves only part (b); the descent and
semisimplicity assertions of Proposition 4.19 are separate obligations.
