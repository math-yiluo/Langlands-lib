# Real norm signs for the normalized CM infinity character

This internal helper evaluates the normalized weight-one infinity character on
principal elements of the maximal real subfield of a CM number field. It
connects the archimedean formulas in `CMHalfWeightInfinity` to the rational norm
criterion needed in the global extension argument.

`realInfinityRestriction t` is the monoid character obtained by including a
nonzero element of the maximal real subfield into the CM field, taking its
archimedean diagonal, and applying the normalized infinity character of `t`.
For a pure weight-one type, `realInfinityRestriction_eq_norm_sign` proves that
its value is the rational norm divided by its ordinary absolute value, both
regarded as complex units. Consequently
`normalizedCharacter_real_diagonal_of_norm_pos` gives value one whenever the
rational norm is positive.

The proof identifies the archimedean places of the CM field with those of its
maximal real subfield through `IsCMField.equivInfinitePlace`. Restriction of a
chosen complex embedding equals the chosen real embedding at the restricted
place. The product of the resulting coordinates is the rational norm, using
the proved place-factor norm product in
`Langlands.ClassField.Global.CyclicReciprocityParts`. The real-coordinate formula
for the normalized character reduces its value to that product divided by its
absolute value. Positivity then makes numerator and denominator equal.

The result assumes positivity when applying the final criterion. It proves no
finite local norm or reciprocity criterion for that positivity, and no existence
of a global Hecke character.
