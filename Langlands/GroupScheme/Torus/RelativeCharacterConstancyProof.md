# Constant actual characters detect diagonalizability

`Langlands.GroupScheme.relativeCharacterConstancy` proves
`RelativeCharacterConstancyStatement.{u}` over any base scheme. It
identifies diagonalizability of a group of multiplicative type with
constancy of its actual relative character presheaf with finitely
generated coefficients.

For a diagonalizable group, the given isomorphism with `D_S(M)` induces
an isomorphism on characters by precomposition. The canonical comparison
`Cartier.DiagonalizableCharacters.charactersIso` identifies the
characters of `D_S(M)` on every test scheme with locally constant
`M`-valued functions.

Conversely, an isomorphism of the actual characters with the constant
model gives an `M`-indexed family of characters. The evaluation map
`Cartier.characterFamilyHom` produces a group homomorphism `H ⟶ D_S(M)`.
Its pullback on a labelled character of `D_S(M)` recovers the prescribed
character. The proof checks this equality by evaluating on arbitrary
smaller tests, including the universal point of the relevant fibre
product. For a locally constant section, restriction to an open fibre
of that section reduces the comparison to a labelled constant. Thus
the induced character map is the given isomorphism after the canonical
comparison for `D_S(M)`.

The character map commutes with base change via the pullback composition
isomorphisms, so it is still invertible on the members of the étale
diagonalizing cover for `H`. The target is diagonalizable on those
members by base change. Between two diagonalizable models the proof
constructs the inverse group homomorphism by evaluating the inverse
character map. Equality on labelled characters gives equality of
group homomorphisms by the description of points of a diagonalizable
group. Descent of isomorphisms along the étale cover then makes the
underlying evaluation map invertible over `S`. The forgetful functors
from groups to monoids and from monoids to the slice category reflect
isomorphisms, yielding the required group isomorphism.

This implements the constant-object consequence of the character
anti-equivalence in Brian Conrad's *Reductive group schemes* (2014),
Proposition B.3.4, pp. 290–292, as used in the proof of Corollary B.3.6,
p. 293. The Lean proof works with the actual relative character
presheaf on all test schemes over `S`.
