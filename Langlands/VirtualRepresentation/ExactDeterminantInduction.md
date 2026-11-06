# Determinant transfer on the actual exact quotient

This derived helper module bundles finite-coset transfer as the multiplicative
homomorphism `ExactGrothendieckGroup.characterTransfer` from complex characters
of a finite-index subgroup to complex characters of its ambient group. Its
value on a character is Mathlib's `MonoidHom.transfer`. The one and product
laws follow by expanding the finite product in the transfer definition.
`characterTransfer_comp` proves compatibility with postcomposition into complex
units by applying `map_prod` to the same finite product.

The provenance is internal algebraic descent from the published modules
`ExactDeterminant`, `ExactInduction`, `ExactRestriction`, and the proposition in
`LocalFactor.Inductive.Statement`. The following induction results retain
`GallagherDeterminantStatement` as an explicit hypothesis. This module does not
prove Gallagher's formula or the additive-character scaling target.

`determinantCharacter_induce_of_gallagher` states the full integer-degree
formula on the genuine quotient by short-exact-sequence relations. The proof
compares integer-linear maps to the additive synonym of the character group.
One map is determinant after exact induction; the other is the sum of the
integer degree times the determinant of the induced trivial line and transfer
after determinant. The quotient's `hom_ext` reduces equality to genuine
representation classes, where the supplied Gallagher formula applies. Equality
on all virtual classes follows by evaluating these equal linear maps.
`determinantCharacter_induce_degreeZero_of_gallagher` evaluates this formula at
degree zero, so the permutation determinant has exponent zero and disappears.
The field is complex; group and representation carrier universes remain
independent, and induction uses the existing maximum carrier universe.

`determinantCharacter_restrict` proves that the determinant of an exact virtual
restriction is precomposition by the given group homomorphism. Precomposition
is bundled as an integer-linear map on additive character groups, and `hom_ext`
again reduces to genuine classes. On a genuine class the two determinants
agree because restriction keeps the action operator at the image group
element. No continuity hypothesis or splitting of exact sequences is used in
these purely algebraic results.
