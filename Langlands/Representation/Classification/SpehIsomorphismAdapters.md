# Actual Speh isomorphism and complementary rank adapters

Author: Worker 1745.

This internal unit derives actual isomorphism adapters from the published
`SpehDatum.IsSpeh` relation, the normalized twisted-product construction,
and the isomorphism invariance of irreducibility. It introduces no assertion
from original literature. All declarations preserve independent universes
`uF` and `uV`, and use smooth complex representations with carriers in
`Type (max uF uV)`.

`SpehDatum.IsSpeh.of_iso` transports the Speh relation from `S` to `S'`
along an actual smooth equivariant isomorphism `S ≅ S'`. It retains the
same discrete-series datum, transports target irreducibility, and composes
the original surjective quotient map with the equivariant equivalence.
Every other irreducible quotient's isomorphism to `S` is composed with the
supplied isomorphism to `S'`, giving the required uniqueness relation.

`SpehDatum.complementaryInducedIso` applies the published
`twistedProductInducedIso` to the uniform two-factor block shape. Both
factors use the same supplied isomorphism. The first exponent remains
`α` and the second remains `-α`.

`SpehDatum.complementaryRankIso` additionally accepts a positive rank `m`,
a displayed equality `h : d.degree = m`, and an isomorphism from the
rank-transported Speh candidate to an actual representation `A` of rank
`m`. Its result is an isomorphism from the entire complementary induction,
transported along `congrArg (fun r => 2 * r) h`, to the entire uniform
product of the two opposite twists of `A`. The proof eliminates the rank
equality and applies `complementaryInducedIso`. The proof of positive
rank in each block shape is propositionally irrelevant.

`isTadicBuildingBlock_complementary_of_spehIso` accepts the same rank
comparison, an actual `d.IsSpeh S` witness, and strict inequalities
`0 < α` and `α < 1/2`. It constructs the complementary alternative of the
published `IsTadicBuildingBlock` predicate using the doubled-rank equality
and `complementaryRankIso`. In particular, it gives the whole induced
representation as the building block and retains the same `S` in both
factors.

The unit constructs no Speh realization for a multisegment socle and
proves no unitarizability or unitary-dual exhaustion assertion. Those
remain separate mathematical obligations.
