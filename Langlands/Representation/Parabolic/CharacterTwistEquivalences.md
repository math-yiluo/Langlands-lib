# Character twists of actual normalized parabolic functors

For an actual ordered GL block shape, an ambient character trivial on the
unipotent radical restricts to a character of its embedded product Levi.
This derived adapter constructs the corresponding representation equivalences
for normalized Jacquet restriction and normalized induction. It includes all
natural ranks, independent field and carrier universes, and the actual
coinvariant and induced-function carriers. No finite-dimensionality,
admissibility, irreducibility or finite-length premise is needed.

`character_eq_leviProjection` proves that the ambient character on the
parabolic factors through the actual Levi projection. The proof uses the
published decomposition into `unipotentPart` times `leviInParabolic`; the
character is one on the first factor by the stated radical-kernel inclusion.

`normalizedJacquetOfCharacterTwistEquiv` applies the published normalized
trivial-radical character-twist equivalence on the parabolic and then
restricts its action along `leviToTop`. The same supplied full positive
modulus appears on both sides. Its map sends the class of every original
vector to the class of that vector, as stated by its `_mk` theorem. The Levi
character is literally the ambient character composed with `leviEmbedding`.
This algebraic quotient equivalence requires neither an open-kernel hypothesis
nor a topology.

For a supplied topological coefficient ring, `restrictSmoothCharacter`
restricts a smooth ambient character to the Levi. Continuity of the embedding
pulls back its open kernel. `inducingRepresentation_characterTwist` proves
that the two actual parabolic covariance actions agree: the ambient character
factors through the Levi projection, and its scalar commutes with the supplied
normalizing scalar.

`normalizedInducedOfCharacterTwistEquiv` first uses the published actual smooth
induction twist equivalence and then the induced equivalence of those equal
covariance actions. The forward map multiplies an induced function's value at
`x` by `χ(x)`, as its `_eval` theorem states. The action remains right
translation. The generic normalizing character is supplied as a smooth Levi
character, so in particular the construction specializes to the existing
positive half-modulus normalization of the actual p-adic functor.

The provenance is internal and derived from the published actual parabolic
factorization, generic induction character-multiplication equivalence,
normalized Jacquet character-twist equivalence, and equivariant-linear
transport. No new original-literature assertion is transcribed. This pair
supplies representation equivalences; it does not assert Aubert equivariance,
a segment socle/quotient switch or analytic classification. The map on exact
finite-length K0 requires the separate actual functor and class adapters.
