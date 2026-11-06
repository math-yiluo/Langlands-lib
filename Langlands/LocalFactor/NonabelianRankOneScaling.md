# Rank-one scaling in the actual exact virtual group

This internal module applies the concrete abelian epsilon scaling theorem to
the actual character classes used by the nonabelian system specification.

The determinant of the universe-lifted scalar character line is the character
itself: each action is a scalar multiple of the identity on a one-dimensional
complex vector space. The proof calculates that determinant directly. The
published exact-quotient evaluation theorem then gives the determinant of the
character class, and the common-closure specialization is the character pulled
back along the supplied reciprocity family.

`additiveCharacterScaling_characterClass` assumes only the system's existing
`RankOneRelation`. It applies that relation at both additive characters and
uses `abelianEpsilonExpression_scale`. The degree of the actual character class
is the published value one. At a Weil lift mapping to the given field unit,
the exact determinant equals the multiplicative character at that unit. This
is exactly the target scaling identity restricted to a character class, for
independent field and representation universes.

No reciprocity family, local-constant system or Weil lift is selected here.
The result is a derived rank-one input to the unchanged proposition
`Langlands.LocalFactor.NonabelianSystem.AdditiveCharacterScalingStatement`.
Its source normalization is Deligne (1973), formula (5.4), as described in the
paired abelian scaling module.
