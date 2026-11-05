# A positive character on independent cocharacters of a split torus

Worker 1633. This is an internal lattice prerequisite for the coefficientwise
moderate-growth argument on actual rational points. It is not attributed to a
separate assertion in the literature.

`Langlands.GroupScheme.PositiveCharacterOnIndependentCocharactersStatement.{u,v}`
quantifies over every field `k : Type u`, every commutative group scheme `T`
over `Spec k` whose underlying group scheme is a split torus, every finite
index type `I : Type v`, and every family `x : I → cocharacterLattice T`
that is linearly independent over the integers. It asserts the existence of
one actual character `α : characterLattice T` satisfying
`0 < latticePairing T α (x i)` for every index `i`. The field and family
universes are independent.

Both lattices consist of actual homomorphisms of commutative group schemes.
The pairing is the integer exponent of the composite from the multiplicative
group to itself. Thus the conclusion concerns an actual character of the
given torus, rather than a functional supplied as an additional premise.
There is no characteristic restriction. Empty families and rank-zero tori
are included.

The internal provenance is elementary finite-rank lattice algebra: after
passing to rational coordinates, extend the functional with value one on
each independent vector to the whole vector space. Clearing finitely many
denominators produces an integral functional with positive values. The
perfect character/cocharacter pairing of a split torus realizes that
functional as a character.

In the surrounding moderate-growth argument this lemma supplies a character
positive on a finite independent family of cocharacter directions. It
asserts no cone decomposition, norm bound, representation estimate, or
coefficientwise moderate-growth theorem.
