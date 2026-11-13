# Positive normalizers and incident facet fixers

This internal construction concerns a supplied `KPBuildingDatum D` for an affine
group scheme over a nonarchimedean local field in arbitrary universe `u`. The
geometric hypothesis is `D.SatisfiesGroupAxioms`, which availability supplies.
All point groups carry the canonical rational-point topology.

`facetPositiveZeroNormalizer D Fa` is the actual normalizer of the facet's
radical preimage, intersected with the actual zero subgroup. The existing
`FacetPositiveTopology` results put that radical preimage in the facet fixer
and make it normal there. The subgroup normalizer criterion therefore puts the
whole facet fixer in `facetPositiveZeroNormalizer`.

The positive subgroup is open. Its containment in the normalizer intersection
makes that intersection open, hence closed, in the ambient point group.
Connected reductivity already carried by the building datum supplies smoothness
and the finite-type hypothesis used for the topology of the rational-point group.

The compactness theorem assumes explicitly that the positive subgroup's
normalizer, intersected with the common kernel of all rational-character norms,
is algebraically bounded. The zero subgroup lies in that kernel by
`ZeroSubgroupDatum.zeroSubgroup_le_rationalCommonNormKernel`. Each regular
function bound therefore restricts to `facetPositiveZeroNormalizer`. The
published local-field boundedness–compactness comparison applies to its closed
carrier and proves compactness.

`positiveNormalizerFacet` applies `compactOvergroupFacet` to this compact
overgroup of the original facet fixer. It chooses a facet `Fb` with
`FacetPrecedes Fb Fa` and retains the equality between its zero fixer and the
positive normalizer intersection. Both the incidence direction and equality
are included in the returned subtype.

This is internal content deduced from the named topology, norm-kernel and
compact-overgroup results; it introduces no new interpretation of a literature
statement. It does not prove the boundedness premise, identify the chosen face
with the original facet, or prove any maximal pro-`p` conclusion. In particular,
the missing normalizer boundedness result remains a separate proof obligation
before this construction can be used in the final theorem without extra premises.
