# Archimedean local components from isobaric witnesses

The real and complex standard-module maps in the isobaric predicate give
irreducible subspaces of the respective place restrictions. Complex
linearity extends the intertwining identities for real Lie directions to
the complexified Lie algebra, so the images are stable under the full place
actions. Irreducibility follows from the condition on stable subspaces of
each image. The surjective map onto the image transfers the real or
complex `(𝔤, K)`-module axioms and admissibility by the quotient lemmas
in `GKModuleQuotient`. The source hypotheses come from the corresponding
standard-module compatibility and admissibility theorems.

When two irreducible subquotients receive maps with irreducible images from
the same standard module, each map has the largest proper stable subspace as
its kernel, provided that subspace exists. The map through the common
quotient sends the first image onto the second and intertwines the compact
and Lie actions. Each image spans its ambient place restriction under
intertwiners from that image. Composing with the map through the quotient
shows that the first image is a common irreducible isotypic type.

The isotypy step uses the Library's place-stability lemmas
`isRealPlaceIsotypic_restrict` and `isComplexPlaceIsotypic_restrict`.
These implement the isotypic restriction argument in D. Flath,
*Decomposition of representations into tensor products* (1979), end of the
proof of Theorem 1, printed p. 180 (PDF 176).

The complex comparison uses `complexStandardLanglandsQuotient`, the
quotient assertion of Knapp (1994), Theorem 4(a), printed p. 405 (PDF
p. 415). The real comparison takes `RealStandardLanglandsQuotientStatement`
as a premise, in the closed positive chamber for the determinant
exponents. The order is weakly decreasing `Re(t_j)` as in Getz–Hahn
(2024), (10.29)–(10.30), p. 283 (PDF p. 295), with quotient and
permutation assertions in Theorem 10.6.1, p. 284 (PDF p. 296). Knapp,
Theorem 1(a), (c), p. 400 (PDF p. 410), gives the corresponding real
assertions with the printed condition (2.5) on `Re(t_j)/n_j`. The
Library's order follows from the root calculation in
[IsobaricAutomorphicRepresentation, §2](IsobaricAutomorphicRepresentation.md#2-the-langlands-order-of-archimedean-blocks).

For permuted ordered lists, `OrderedStandardPermutation` gives a bijective
intertwiner between the standard modules. The real Mœglin-data variant
allows the weight-sign and weight-zero changes by first normalizing both
lists. The proof precomposes the second standard-module map with a
surjective intertwiner, preserving its image and its irreducibility.
The complex permutation comparison corresponds to Knapp, Theorem 4(c),
printed p. 405 (PDF p. 415).
