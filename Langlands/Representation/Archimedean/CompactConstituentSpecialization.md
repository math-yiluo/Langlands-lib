# Compact types in specialization of simple constituents

The transfer criterion for affine families requires a finite-rank operator
that acts nontrivially on the constituent. For a locally finite admissible
compact action with continuous coefficients, the isotypic projections in
`KFiniteDual` supply such an operator. Given a vector with nonzero image in
the constituent, sum the finitely many projections in its isotypic
decomposition. The sum fixes the vector, has finite-dimensional range, and
preserves every compact subrepresentation. In particular it preserves the
source of the quotient map and the kernel of that map, so it acts on the
constituent as well.

Transport the projection to the second module using one compact intertwining
isomorphism. Every other such isomorphism transports it to the same operator
because the sum of isotypic projections commutes with all compact intertwining
endomorphisms. Adjoin the projection as an extra generator of the free algebra
and apply `isConstituent_of_affine_isomorphisms` at zero. Restriction to the
original compact and infinitesimal generators gives the required stable
subspace and equivariant surjection in the second module.

This is a derived argument for families of operators. Its intended application
is the comparison between orders of normalized archimedean induction in
Badulescu–Renard (2010), Remark 2.3 and Proposition 2.4, pp. 1123–1124
(PDF pp. 10–11). The compact hypothesis uses admissibility in the form of
Getz–Hahn (2024), Definition 4.4.4 and p. 116.
