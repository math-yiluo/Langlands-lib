# Positive forms from compact coefficients on the actual norm kernel

This derived supporting construction supplies an invariant positive form on
the original carrier of an irreducible smooth complex representation. It is
intended for the zero-exponent branch of rational rank-one self-association.
It composes published constructions and has no new literature claim.

The generic definition `UnitaryCentralCharacter.compactRestrictionPositiveForm`
assumes a locally compact Hausdorff topological group, an irreducible smooth
representation, a supplied unitary character acting on its full group center,
and a normal subgroup `H` such that `H` joined with that center has finite index.
It also assumes compact smooth-dual coefficients on the restriction to `H`
and cofinality of compact open subgroups. It does not require admissibility,
second countability, or unimodularity.

The proof first observes that the full center is closed, so its group quotient
is Hausdorff and locally compact. The published compact-open separation theorem
`exists_nonzero_smoothDual_of_irreducible_compact_cofinal` supplies a nonzero
smooth functional. Continuous restriction makes this functional smooth for
`H`, so the compact-coefficient hypothesis applies to every vector.

The published generic lemma
`UnitaryCentralCharacter.hasCompactSupport_coefficientNorm_of_finiteIndex`
then gives compact support for the descended coefficient norms on the full
central quotient. Although its source file
`LeviCuspidalRealUnitarizationProof` concerns general linear groups elsewhere,
this lemma applies to arbitrary groups and is reused unchanged.
Smoothness gives continuity of each descended norm. Its compact support makes
it square integrable against inverse left Haar measure on the quotient.
This measure is right invariant and positive on nonempty open sets.
The published `UnitaryCentralCharacter.coefficientProductForm` integrates the
conjugate-first coefficient product and proves definiteness using irreducibility
and the nonzero functional. The result is an actual `InvariantPositiveForm`,
rather than just a square-integrability predicate.

The rational specialization `rationalNormKernelPositiveForm` uses the actual
point group of an affine group scheme with its canonical point topology.
The field and representation carrier have independent universes `u` and `v`.
Local compactness, the nonarchimedean group property, and Hausdorffness of that
point group are explicit assumptions. No split or characteristic-zero
restriction is imposed.

Its additional inputs are a central morphism from a commutative group scheme,
finite index of its actual image in the rational-character valuation image,
an irreducible smooth object, a supplied full unitary central character, and
compact smooth-dual coefficients after restriction to the actual
`Plancherel.rationalCommonNormKernel`. The map need not be assumed injective
or a torus for this consumer. The published
`Plancherel.finite_rationalCentralQuotient` makes the quotient by the norm
kernel joined with the point-map image finite. Centrality places that image
inside the full abstract center, hence the join with the full center also
has finite index. Compact open cofinality follows from the locally compact
nonarchimedean group assumptions. The generic positive-form definition now
applies. `isUnitarizable_of_compact_normKernel_restriction` records its
nonempty conclusion.

This unit does not prove compact restriction from cuspidality or establish the
central valuation index. It does not construct a unitary central character
from split-center exponent data or transport a literal Levi representation
to the canonical Levi point group. Those are separate obligations. In
particular, this supporting construction does not prove
`RationalRankOneSelfAssociationStatement` or add any premise to that target.
