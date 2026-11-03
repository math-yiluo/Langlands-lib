# Cyclic comparison on actual relative roots

`ActualRootCyclicComparisonStatement` is the restriction of the existing
`CyclicRootFunctorComparisonStatement` to a connected reductive group, a
maximal split torus, and an actual relative root. It retains every field,
arbitrary universe, all test schemes, and every positive integral multiple
in the cyclic tail. The broader published cyclic statement also covers
smooth affine groups and nonzero characters that are not relative roots;
the restricted statement makes no claim about those cases.

`actualRootCyclicComparison_of_realization_uniqueness` proves this restricted
statement from the two explicit structural premises
`SemigroupRealizationStatement` and `RootSubgroupUniquenessStatement`.
Neither premise is proved in this module, and this theorem does not discharge
the unconditional ordered-product target.

Semigroup realization gives a smooth connected closed representative of
the first cyclic term, its stability under conjugation by the split torus,
and its exact tangent image. A private unconditional span equality
identifies that tangent image with `positiveWeightSpan i a`. The represented-range equality
transports stability and the tangent-image assertion to the chosen
representative. Actual-root uniqueness then identifies its range with
`subgroup i a`, and transitivity gives equality of the all-test functors.

The span argument is adapted from the shared draft of Workers 1286 and 1302
for task `da2124be-bd33-448b-8c2d-4a74c4811fec`, revision 1; its generic
cyclic-tail reindexing is due to Worker 1302. Here the published
`semigroupWeightSpan_conjugation` first changes intrinsic action weights to
adjoint weights. Each character in `cyclicTail a 1` has a positive natural
multiplier, and each positive multiplier defines a character in that tail.
The two supremum inequalities give exactly the full positive integral span.
Repeated characters do not affect either inequality, so this equality
permits even the zero character and needs no root or splitness hypothesis.
The calculation is private to this module and introduces no duplicate
public span declaration or dependence on an unpublished module.

The provenance is internal: this is a direct implication between existing
Library predicates. In particular, a proof of root uniqueness that itself
assumes the full cyclic comparison cannot use this restricted reverse
implication to discharge that assumption.
