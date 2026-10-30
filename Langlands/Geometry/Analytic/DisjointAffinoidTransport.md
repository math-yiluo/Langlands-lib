# Transport of the constructed disjoint affinoid atlas

Author: Worker 36.

This module constructs an affinoid atlas on any space equipped with a
homeomorphism from the actual disjoint union of a family of presented
affinoid spectra. The algebras, restrictions, factorization and algebra
coherence come from the published concrete disjoint atlas. No atlas or
analytic-property certificate of the target space is an input.

## Sources and provenance

The original atlas definition is Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), section 1.2, Definition 1.2.3,
printed page 16 / PDF page 13. It assigns an affinoid algebra and a
spectrum homeomorphism to each member of a compact net on a locally
Hausdorff space, and bounded domain restrictions to containments.
Remark 1.2.4(i) states the restriction composition law.
Registered original: `berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

The affinoid-domain test condition is Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), Definition 2.2.1, printed/PDF page 9:
every affinoid morphism whose image lies in the closed domain factors
uniquely through its defining affinoid morphism. This quantifies over
all affinoids, including nonstrict ones.
Registered original: `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Both passages were read in the originals. No source-specific errata
note was present in the current Library.

The transport is a derived implementation of these definitions for the
constructed disjoint atlas, not a separately stated result in the
sources. It imports `DisjointAffinoidAtlas` by Lean name and retains
its actual finite positive-polyradius closed quotient algebras.

## Transported charts and topology

Work in `Langlands.Analytic.DisjointAffinoidAtlas`. Let
`A : I → PresentedAffinoidAlgebra K` and let
`e : Space A ≃ₜ X`. The coefficient field is ultrametric and normed;
the atlas constructor also requires its completeness. The index type,
target space and coefficient field have independent universes.
`Space A` is the actual topological sum of the actual quotient spectra.

`transportChart A e c` is `e ∘ chart A c`, with the original
`ChartIndex A` and `chartAlgebra A c`. These indices retain precisely
the nonempty component spectra. `transportChartDomain` is its range,
and `transportChartFamily` is the family of such ranges. The original
component inclusion is an open embedding, so its composite with `e`
is one as well.

`preimage_transportChartDomain` proves that pulling back each transported
domain along `e` gives the original component domain; the reverse range
implication uses injectivity of `e`. Hence
`chartDomain_subset_of_transportSubset` pulls chart containments back.
`transportChart_eq_of_mem_inter` pulls a common point back using
`e.symm` and uses the disjoint-component equality.
`transportChart_eq_of_subset` uses the original nonempty-component
containment result. This yields `transportChartDomain_injective`.

`transportChartFamily_covers` takes the component of `e.symm z` and
applies `e` to its chart equation. For the quasinet condition, the
single open chart containing `z` gives a finite family whose union is
a neighborhood. For the net condition on pairwise intersections, a
point in the intersection forces equal chart indices. The component
then belongs to the restricted family as the whole intersection
subspace, giving its quasinet. Empty intersections have no points to
check. Thus `isNet_transportChartFamily` is proved directly, without
assuming a net on `X`.

## Bounded restrictions and factorization

`transportRestriction A e c d h` is the original bounded restriction
on the original quotient algebras, with containment pulled back along
`e`. `transportRestriction_chart` applies `e` to the already proved
restriction chart equation. It therefore realizes the inclusion of
the transported domains.

`transportRestriction_universal` reuses the original stronger
factorization theorem: for every normed commutative `K`-algebra `R`
in an independent universe and every bounded homomorphism `φ` out of
the containing chart algebra, there is a unique bounded `ψ` such that

`ψ.comp (transportRestriction A e c d h) = φ`.

This theorem needs no spectrum-image condition: contained nonempty
components have equal indices, and their restriction is the bounded
identity transported along that equality. It therefore specializes to
all presented positive-polyradius affinoid tests required by
`IndexedAffinoidAtlas.restriction_universal`, with its image condition.
The self-restriction and composition laws reuse the original algebra
identities. No equality of algebra maps is inferred from their action
on spectrum points.

`transportAtlas` assembles the constructed charts, injective domain
indexing, net and restrictions into `IndexedAffinoidAtlas K X`.
The sum is Hausdorff, and `e` transports that property to `X`; the
whole space supplies each Hausdorff neighborhood. Compactness and
Hausdorffness of every chart follow from the spectrum embedding via
the published `IndexedAffinoidAtlas.isCompactFamily_chartFamily`.
Its `range_restriction` and `isClosed_relativeDomain` likewise supply
the relative image and closedness parts of the domain condition.

## Scope

The construction allows empty index types and empty spectra. It
transports this particular constructed disjoint atlas; it does not
assume or transport an arbitrary analytic atlas. Proper overlapping
domain restrictions, refinements, analytic gluing, the general
strong-morphism localization, structure sheaves, etale sites and
Harris's local tower remain separate host-task obligations.
