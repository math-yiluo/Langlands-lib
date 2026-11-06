# Lower-rank arithmetic Weil pair factors

This module supplies the arithmetic lower-rank L-factor step for an actual
finite p-adic field `F`. Its statements are uniform in the field universe.
The representation lemmas allow independent carrier universes for their two
factors. The class-level arithmetic interface uses the common carrier universe
required by `arithmeticPairLFactor`.

`HasTrivialLowerRankWeilPairLFactors F σ` is the proposition that the
zero-monodromy pair associated to a continuous irreducible Weil class `σ` of
positive rank `n` has arithmetic pair L-factor equal to one against every
continuous irreducible Weil class of positive rank `m < n`.
`hasTrivialLowerRankWeilPairLFactors` proves this proposition for every `σ`.
The directly usable equality is
`arithmeticPairLFactor_weilPairClass_eq_one`.

## Implemented argument

`lowerRank_invariantHom_eq_bot` proves that the inertia-fixed part of
`Hom(A,B)` vanishes when `A` is an irreducible finite-dimensional complex
representation of the actual local Weil group and `rank B < rank A`.
Neither continuity nor irreducibility of `B` is required.

Suppose that this invariant space is nonzero. Geometric Frobenius acts on it,
so algebraic closedness of the complex numbers provides a nonzero eigenvector
`f`. The private helper `eigenvector_zpow` shows that its eigenvalue is nonzero
and computes the action of every integer power of Frobenius. Every Weil group
element is an inertia element times a Frobenius power, as follows from the
degree of the chosen Frobenius and the definition of inertia. Consequently,
each Weil element acts on `f` by a nonzero scalar.

The linear kernel of `f` is therefore a Weil subrepresentation of `A`.
Irreducibility makes this subrepresentation either zero or the whole space.
The second case contradicts `f ≠ 0`. The first makes `f` injective, contrary
to the finite-dimensional rank inequality. Hence the inertia-fixed Hom space
is zero.

`lowerRank_invariantTensor_eq_bot` applies this result to the dual of `A`.
The published dual irreducibility and rank lemmas apply, and the double-dual
equivalence together with tensor–Hom adjunction identifies `A ⊗ B` with
`Hom(A dual,B)`. The intertwining equivalence transports inertia-fixed vectors,
so the tensor invariant space also vanishes.

`eulerPolynomial_eq_one_of_invariantSubspace_eq_bot` observes that the
inertia-fixed monodromy kernel is zero whenever the full inertia-fixed
representation space is zero. Its Frobenius operator thus acts on a
zero-dimensional vector space. The Euler polynomial is the reverse of its
characteristic polynomial, hence is one.
`lowerRank_pairLFactor_eq_one` applies this to the tensor of two Weil–Deligne
representations. It assumes irreducibility of the first underlying Weil action
and a strict rank inequality, with no parameter, continuity or monodromy
hypothesis. The pair L-factor is the inverse of the Euler polynomial in
`RatFunc ℂ`, so it is one.

Finally, `arithmeticPairLFactor_weilPairClass_eq_one` chooses representatives
of the two continuous irreducible Weil classes. The quotient rank conditions
give the required strict inequality; both representatives are equipped with
zero monodromy by `weilPairClass`. The preceding pair-factor theorem gives
the class-level equality. The final predicate and theorem package these
equalities for all smaller positive ranks.

## Provenance and scope

This is an internal consequence of the existing actual local Weil degree and
inertia definitions, complex finite-dimensional linear algebra, the published
dual and tensor interfaces, and the arithmetic factor definitions. The proof
above is the implemented argument; no external classification or correspondence
theorem is used.

This module supplies a supporting arithmetic ingredient for the extension
argument. It does not prove that images of an arbitrary factor-compatible map
are supercuspidal or that they equal the given supercuspidal correspondence.
The unchanged `FullCharacterizationExtendsStatement` remains a separate proof
obligation.
