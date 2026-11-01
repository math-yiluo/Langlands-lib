# Localization of fixed-original-chart domains and covering families

For an actual indexed affinoid atlas `a` over a complete ultrametric normed
field, this module identifies domains of its constructed subspace atlas with
ambient original-chart domains contained in the subspace. It also compares
the covering families defined by the published quasinet topology.
The coefficient, point and original chart index universes remain independent.

## Source context and provenance

The source is Vladimir G. Berkovich, *Etale cohomology for non-Archimedean
analytic spaces*, Publications mathematiques de l'IHES 78 (1993), section 1.3,
Definition 1.3.1, printed page 23 / PDF page 20, and the G-topology paragraph
on printed page 25 / PDF page 22. The registered source is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The quasinet convention is section 1.1, printed page 13 / PDF page 10.

The source constructs domains using contained affinoid domains and defines
coverings by quasinet families of domains in a target domain. The present
construction is derived for the already published, restricted category
`OriginalChartDomain a`: its objects are actual subsets locally covered by
contained **original** charts of `a`; its arrows are inclusions. It uses
`AtlasSubspaceRestriction`, `OriginalChartDomains`, `OriginalDomainTopology`
and the paired internal `AtlasTopology.NestedRestriction`.

This does not identify the fixed-original-chart category with all analytic
domains of a saturated atlas. General analytic-domain descent, the structural
sheaf, saturation and etale or equivariant sites remain separate obligations.

## Objects and arrows

`isOriginalChartDomain_subspaceAtlas_iff` proves that a subset `U` of an
original-chart domain `S`, with the actual induced topology, is an
original-chart domain for the constructed atlas on `S` if and only if
its ambient image is an original-chart domain for `a`. The chart-family
identity from `AtlasSubspaceRestriction` reduces this to nested restriction of
contained-member families. The helper proves the required equivalence using
the actual nested subtype homeomorphism and quasinet invariance under that
homeomorphism.

`subspaceExtend` takes this ambient image and proves it lies below `S`.
`subspaceRestrict` takes the preimage in `S` of an ambient domain below `S`.
The domain condition follows from the preceding equivalence, using that
image of preimage recovers a subset contained in `S`.

The two roundtrip theorems use injectivity of subtype inclusion and the
containment hypothesis. Ambient image also preserves and reflects subset
inclusion, as `subspaceExtend_le_iff` states.
`localizationOrderIso` therefore constructs an order isomorphism from domains
of the subspace atlas to `Set.Iic S` in the ambient domain order.
`localizationEquivalence` is its induced equivalence of inclusion categories.
`subspaceExtensionFunctor` composes the object extension with the ambient
inclusion category, sending an arrow to the corresponding subset inclusion.

## Covering families

`ofArrows_subspaceExtend_mem_iff` treats any indexed family of arrows into a
domain of the subspace atlas. Its generated sieve covers for the subspace
quasinet topology exactly when the generated sieve of the extended ambient
arrows covers the extended target for the ambient quasinet topology.

The proof applies the published exact criterion
`ofArrows_mem_iff_isQuasinet` on both sides. The helper
`isQuasinet_restrictedFamily_subtype_images_iff` then compares the two actual
target subspaces and their member families, and the image of the range of a
family is the range of its images. This retains the full finite-neighborhood
condition rather than replacing covering by pointwise coverage.
There is no nonemptiness or finiteness assumption on the index type or target.

The categorical equivalence and covering-family comparison are proved
explicitly. This module does not construct an equivalence of sheaf categories
or assert descent for bounded maps to arbitrary analytic targets.
