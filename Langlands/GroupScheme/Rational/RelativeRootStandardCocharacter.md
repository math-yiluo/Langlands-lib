# Standard cocharacters under the relative-root-system hypothesis

Worker 185. This is an internal adapter between the published
`HasRelativeRootSystem`, `simpleRelativeRoots`, and split-torus interpolation
interfaces. The root-system realization is an explicit hypothesis throughout.
The module does not discharge `RelativeRootSystemStatement` and does not
prove any dynamic-subgroup comparison.

`HasRelativeRootSystem.neg_mem_relativeRoots` transfers closure under
negation from the supplied root pairing to the actual character-valued
roots. The root image equality and injectivity of rationalization for a split
torus identify the resulting actual character with the negative character.

`HasRelativeRootSystem.linearIndependent_simpleRelativeRoots` uses the
finite crystallographic root pairing supplied by that predicate. Its root
image is exactly the rationalization of the actual character-valued relative
roots. The proof extends the integral pairing with the given generic
cocharacter to a rational functional on the character space, then restricts
it to the relative-root span. Genericity makes this functional nonzero on
every root of the supplied root pairing.

Each actual simple root lifts to an index of the root pairing. The lift is
indecomposable among the positive roots: a decomposition would pull back
to a decomposition of the actual character into two positive actual roots,
contradicting its definition. This pullback uses injectivity of
rationalization for the character lattice of a split torus. Mathlib's
`RootPairing.linearIndepOn_root_baseOf` proves independence of these
indecomposable positive roots. That theorem does not assume reducedness.
Restricting its independent family along the injective lifts and embedding
the relative-root span into the rational character space gives the claimed
independence.

`HasRelativeRootSystem.exists_standardCocharacter` applies the lattice
interpolation result from `IndependentStandardCocharacter`.
`standardCocharacterOfRelativeRootSystem` chooses the resulting cocharacter;
its specification proves the published `IsStandardCocharacter` predicate.
The result includes empty simple-root sets and every subset of the simple
roots. It imposes no condition on the characteristic of the underlying
field and does not require the supplied root system to be reduced.

An unconditional reductive-group proof must still produce the actual
`HasRelativeRootSystem` realization from connected reductivity and a maximal
split torus. This conditional construction supplies no replacement for that
structural obligation.
