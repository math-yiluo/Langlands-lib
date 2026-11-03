# Borel maximality of an intersection from a closed product

Internal supporting construction by Worker 1438. This module combines the
published existence of homogeneous quotients with the actual quotient
properness construction in `CentralizerProductProperness` and the explicit
proper-solvable-quotient criterion in `ProperSolvableQuotient`. The included
unchanged homogeneous closed-immersion helper credits Worker 716 for its
adapted generic-flatness covering argument.

For actual group-scheme maps `j : M → G` and `b : B → G` over a field in
arbitrary universe, `intersectionFst_isClosedSubgroup` proves that the first
projection of their actual pullback is closed when `b` is closed. This is
base change of the closed immersion `b`. If `M` is smooth and affine and the
actual intersection is smooth, `intersectionQuotient` chooses its actual
homogeneous quotient using `smoothSubgroupQuotientExistence`. It retains the
published `HomogeneousQuotient` structure, including a separated finite-type
quotient, a smooth surjective quasi-compact projection, and exact right-coset
fibers on every test scheme.

Over an algebraically closed field, assume `M` is connected, both subgroup
maps are monic, and an actual proper ambient quotient `q : G → Q` is supplied.
The ambient projection is smooth, surjective and quasi-compact and has exact
right-coset fibers for `b` on every test scheme. Closedness of the actual
multiplication image `M × B → G` then implies properness of the chosen
intersection quotient, by
`intersection_quotient_isProper_of_product_closed`. This uses the actual
comparison morphism and its proved closed immersion.

If the intersection is also connected and solvable, the supplied hypothesis
`ProperSolvableQuotientBorelStatement` applies to this proper quotient and
proves that the actual first projection is Borel.
`exists_isBorel_of_product_closed` takes this intersection itself as the
desired Borel of `M`; the published all-test range identity for the pullback
gives its prescribed containment in `B`.

The proper-solvable-quotient statement is an explicit input, not a theorem
proved here. Properness of the ambient quotient, closedness of the product,
and smoothness, connectedness and solvability of the intersection also remain
inputs. No cocharacter, centralizer property, or proof of
`CentralizerBorelIntersectionStatement` is asserted in this supporting module.
