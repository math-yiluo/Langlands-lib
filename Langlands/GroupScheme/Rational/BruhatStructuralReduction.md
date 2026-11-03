# Rational Bruhat assembly from the explicit structural propositions

This internal composition connects the published rational Bruhat covering
construction to the opposite-cell contraction construction. Its final
conclusion is the existing `RationalBruhatStatement.{u}` under five
explicit structural propositions in the same arbitrary universe `u`:

- `OppositeCellStatement`;
- `GenericCentralizerStatement`;
- `GenericMinimalParabolicStatement`;
- `ParabolicIntersectionCentralizerStatement`;
- `MinimalParabolicSplitTorusConjugacyStatement`.

`RationalBruhatStructuralInputs` is a proposition-valued structure whose
five fields are exactly these propositions, with no further assumptions
or conclusions. It records the remaining structural obligations in one
input package. The method
`RationalBruhatStructuralInputs.rationalBruhatStatement` consumes a
supplied package by applying `rationalBruhatStatement_of_structural`
to its fields. This unit constructs no inhabitant of the package.

The first theorem,
`hasRationalBruhatDecomposition_of_parabolicCovering_and_oppositeCell`,
works over an arbitrary field with a smooth affine ambient group and a
commutative source group. It takes an actual cocharacter, the opposite-cell
proposition, the equality of its dynamic centralizer with the whole-source
centralizer, and covering by actual dynamic-parabolic double cosets of
normalizing rational points. The opposite-cell specialization supplies
`HasNormalizerProductContractions`. The published contraction assembly
converts the covering to unipotent covering using the two rational Levi
factorizations and supplies all-test opposite-cell injectivity from
affineness. Its conclusion is the existing
`HasRationalBruhatDecomposition i ν`, including the equality criterion for
the actual relative Weyl quotient.

For `rationalBruhatStatement_of_structural`, the proof introduces exactly
the field, connected reductive group, maximal split torus and generic
cocharacter quantified by the imported statement. Smoothness and
affineness come from the connected reductive group. The supplied
`GenericCentralizerStatement` gives the required centralizer equality.
The other three covering propositions feed
`rationalBruhatCovering_of_structural`: generic minimality represents the
dynamic parabolic by a minimal parabolic, common tori compare it with
its conjugates, and conjugacy inside those parabolics gives the
normalizing point and both parabolic factors. The preceding local
assembly then proves the desired instance.

The provenance is internal composition of the named imported
constructions. This unit neither changes the imported Bruhat proposition
nor proves any of the five displayed structural propositions. Each
remains a mathematical input to this conditional theorem and must be
proved before the full Bruhat proof task can be completed. There is no
additional splitness, perfectness, characteristic, field-size or
local-field premise.
