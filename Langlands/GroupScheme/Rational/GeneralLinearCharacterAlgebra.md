# Algebra for rational characters of GL

This internal prerequisite supports the determinant classification of rational
characters in Renard, *Représentations des groupes réductifs p-adiques* (2026),
V.2.2, printed p.105, and the character constructions in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques d'après Harish-Chandra*
(2003), I.1, printed pp.238–239.

These are derived algebraic lemmas, not quotations of assertions at those
locators. Specialization of the universal matrix to the identity gives
determinant one, so its polynomial determinant is nonzero over every nontrivial
ring. The published determinant-localization equivalence then identifies the
GL coordinate ring over a domain with the localization of a polynomial domain
at a nonzero element, proving that it is a domain.

`CharacterFunctionField n R` is its fraction field. The construction
`characterGenericPoint n R` maps the published universal GL matrix into this
field. The coordinate-ring map to that field is injective, so equality after
this passage implies equality in the original coordinate ring. This construction
is internal infrastructure for the GL character proof, rather than a
classification theorem.
