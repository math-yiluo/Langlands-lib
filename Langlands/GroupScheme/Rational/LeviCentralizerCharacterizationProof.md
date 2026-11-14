# Rational Levi subgroups and centralizers of their split components

This module proves the existing proposition
`Langlands.GroupScheme.LeviCentralizerCharacterizationStatement`, uniformly in
the field universe `u`, by the theorem `leviCentralizerCharacterization`.
Its target is the characterization in Renard V.3.1 already recorded in
`ParabolicSplitComponentStatements`. No additional mathematical hypothesis is
retained.

For the forward implication, choose a split component of the supplied rational
Levi using `splitComponentStatement`. Present the original rational parabolic
by a ground-field cocharacter using `parabolicDynamic`. The existing theorem
`IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic`
identifies the centralizer of the chosen split component with the original
Levi image on every test scheme. The composite of the closed split-component,
Levi, and parabolic embeddings is closed. Together with monicity of the Levi
embedding, this gives exactly the requested centralizer representation and
factorization.

For the reverse implication,
`IsSplitTorus.exists_cocharacter_centralizer_eq` supplies a cocharacter whose
dynamic centralizer equals the supplied whole-torus centralizer. Use the
canonical affine representatives of its dynamic parabolic and unipotent
subgroup, and factor both the supplied centralizer representative and the
unipotent representative into that parabolic. The published theorems
`dynamicCentralizerReductive` and `dynamicGeometricUnipotentRadical` give
connected reductivity and the full geometric radical property.
`Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical` then constructs
the rational Levi, using the dynamic multiplication isomorphism. Finally,
`parabolicDynamic` shows that the constructed parabolic is geometrically
parabolic. This implication only needs the split torus and its centralizer
representation; the specified split-component factorization is part of the
target but is not needed in this direction.

The proof is an assembly of the cited published Library theorems. It adds no
definitions and does not prove the other propositions of
`ParabolicSplitComponentStatements`.
