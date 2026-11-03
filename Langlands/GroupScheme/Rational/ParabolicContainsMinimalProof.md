# Minimal rational parabolics inside rational parabolics

This module proves the existing universe-general
`Langlands.GroupScheme.ParabolicContainsMinimalStatement`.
It is an internal prerequisite for the reduction to minimal parabolics in
Borel–Tits, *Groupes réductifs* (1965), Corollary 4.18, printed page 92.
The proof here uses the Noetherian coordinate ring rather than a
classification of parabolic subgroups.

A connected reductive group is affine and smooth over its ground field,
so its coordinate ring is Noetherian. Consider the ideals defined by all
actual rational parabolics whose subgroup functors lie in the given
parabolic. This set is nonempty and has a maximal element. Choose a
parabolic realizing that ideal. Any smaller rational parabolic induces a
larger ideal, which must equal the chosen ideal. Their ideal sheaves are
then equal because the ambient scheme is affine. The factorization of
closed subgroup inclusions is an isomorphism, so their ranges agree on
every test scheme. This proves minimality in the published sense.

The argument uses no generic cocharacter, Bruhat decomposition,
rational-point density, or restriction on the field.
