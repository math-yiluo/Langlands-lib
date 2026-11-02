# Determinant powers on affine points

This derived GL case of the rational-character discussion in Renard (2026),
V.2.2, printed p.105, and Waldspurger (2003), I.1, printed pp.238–239, concerns
actual group-scheme morphisms from GL to the published multiplicative group.
The coefficient ring is an arbitrary integral domain.

Equality of characters on all affine matrices detects equality of the original
scheme morphisms: evaluate on the universal matrix, which corresponds to the
identity point of the affine GL scheme, then use the multiplicative-group
point equivalence.

`coordinateCharacterExponent` is the integer detected by restricting the
character to one coordinate cocharacter and applying the published
classification of multiplicative-group endomorphisms. The resulting exponent
gives the value of the character on every matrix over every test algebra as
the same power of the determinant.

The proof first works over `CharacterLargeField`, the fraction field of the
polynomial ring in one variable over the GL coordinate ring. The extra
variable supplies an element different from zero and one, in every
characteristic. The abstract matrix factorization lemma and the coordinate
cocharacter formula establish the power formula over that field. The map
from the GL coordinate ring to the field is injective, so the equality holds
on the original universal matrix. Every invertible matrix over every test
algebra is a specialization of this universal matrix; naturality proves
the formula there as well. Thus nonreduced test algebras are included.

For an empty matrix index the group of invertible matrices is trivial and
every character value is one; exponent zero gives the asserted power formula.
The theorem in this file states equality on all affine matrix points.
