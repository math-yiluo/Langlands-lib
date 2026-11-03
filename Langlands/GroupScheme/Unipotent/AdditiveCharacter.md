# Nontrivial additive characters of affine unipotent groups

Worker 1448. Derived helper for the unipotent split-series proof.

A nonzero primitive coordinate produces an actual nonzero homomorphism to
`VectorGroup.groupScheme k 1`. The primitive tensor identity gives the
pointwise additive identity through convolution of classifying algebra maps.
The existing vector-group construction then gives the scheme morphism.
Its nontriviality is checked at the universal affine point.

For a corepresented group, if every coordinate lies in the constant line,
all classifying algebra maps agree, so every test point is the identity.
The contrapositive supplies a nonconstant coordinate for any group whose
all-test identity range is nontrivial. The previous primitive-coordinate
theorem applies using coordinate unipotence.

The main perfect-field splitness statement remains a separate obligation.
This file asserts no flatness, surjectivity or smoothness of the character.

The final theorem `Unipotent.exists_additive_character` covers every affine
group scheme over any field, with the unchanged `IsUnipotent` predicate and
`SubgroupFunctor.range (𝟙 U) ≠ ⊥` as its only mathematical premises.
There is no smoothness, connectedness or perfectness assumption. It uses the
existing `AffineCoordinates.groupSchemeIso` to apply the corepresented
result, transports the length-zero triviality condition through that
isomorphism, and composes the resulting character with the inverse
isomorphism. Cancellation proves the resulting character remains nonzero.

The auxiliary theorem
`exists_additive_character_of_isUnipotent` states the same conclusion for an
explicit corepresentation. The theorem
`range_id_eq_bot_of_all_mem_constants` supplies its nonconstant coordinate
premise by comparing every pair of classifying algebra maps on constants.
The construction is derived internally from the existing coordinate,
primitive-element and vector-group interfaces and uses no external
classification theorem or Borel-conjugacy result.

`nonzeroAdditiveCharacter hU hnt` is the named construction: it chooses
one of the characters proved to exist and returns it together with its
nonzero certificate. No quotient or regularity property is added by this
packaging.
