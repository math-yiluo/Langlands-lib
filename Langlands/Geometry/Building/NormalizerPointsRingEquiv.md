# Reflection of rational normalizer points under field extension

This internal prerequisite for Task 5428 compares the actual rational normalizer
subgroups. It assumes the original inclusion is a monomorphism and works for
any extension of fields when reflecting membership of an original point.

For `mem_normalizerPoints_rationalExtend_iff`, the forward implication starts
with the normalizing automorphism after extension. The field extension is fpqc
by `fieldExtension_fpqc`. The existing
`subgroupConjugacyIsoOfBaseChange` descends the source isomorphism conjugating the
inclusion to itself, since the conjugating point is already rational.
`CommGroupScheme.isoOfGroupIso` turns this descended group isomorphism into
the required automorphism in the commutative group's additive notation.
Its defining equation is precisely `IsNormalizingPoint`.
The reverse implication uses `IsNormalizingPoint.rationalExtend`.

If the algebra map is bijective, `normalizerPointsFieldExtend_bijective`
combines this membership reflection with
`GaloisPointComparison.rationalExtend_bijective_of_bijective`.
`normalizerPointsFieldEquiv` bundles the existing normalizer extension homomorphism
as a multiplicative equivalence, whose ambient forward map is definitionally
`rationalExtend`. No reductivity, valuation, or apartment axiom is used.
