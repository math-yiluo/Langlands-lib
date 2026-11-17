# Coordinates of diagonalizable translation graphs

For any commutative base ring R, any abelian group M, and any commutative
R-algebra B, `productAlgebraIso` identifies R[M] tensor_R B with B[M].
The forward map evaluates the first tensor inclusion at the universal
character and the second at constant coefficients. Its inverse evaluates
B[M] using the two tensor inclusions. The inverse identities follow on
monomials and on coefficients, and then by the tensor and group algebra
universal properties. `algebraProductIso` takes spectra and compares this
with D_R(M) times Spec B; its two projection lemmas identify the character
point and the coefficient map.

For an affine group scheme G over Spec R, `translationProductIso` and
`affineSquareIso` compose these comparisons with the actual coordinate
scheme isomorphism of G. The projection lemmas express their agreement
with every affine algebra-valued point.

For any character action, `graphMap` is the R-algebra map
A tensor_R A to A[M] which sends a tensor b to the product of the constant
monomial of a and the coaction of b. `graphMap_hom_eq` identifies it with
the previously constructed strong-grading graph, after restricting scalars.
For a homomorphism i from D_R(M) to G, `map_graphMap_ofTranslation`
identifies its spectrum with the actual graph (h,g) mapped to (g,i(h)g),
under the two spectrum comparisons. This equality is proved by checking
the two product projections and applying the established compatibility
between the coordinate translation action and actual scheme points.

If i is a closed subgroup, the actual graph is a closed immersion by
`Translation.isClosedImmersion_graph`. Conjugating by the spectrum
comparisons proves the coordinate graph spectrum is a closed immersion,
so its algebra map is surjective. `graph_surjective_of_isClosedSubgroup`
then removes the coordinate wrappers. Finally `isStrong_ofTranslation`
applies `strong_of_graph_surjective` to the grading identities already
proved for the translation coaction, obtaining finite degree m/-m
partitions of unity for every m.

These are internal derived comparisons for Task 7326, following the
algebraic quotient route of SGA 3, Exposé VIII, §§4–5, especially
Theorem 5.1. No finite generation, torsion freeness, smoothness, reducedness,
normality, or field assumption is used. This module closes the passage
from closed subgroup geometry to strong grading; it does not yet
construct the scheme quotient or the group structure on it.
