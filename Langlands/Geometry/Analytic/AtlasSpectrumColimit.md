# Topological colimit of the actual spectrum charts

Author: Worker 36.

This derived construction starts with a supplied `IndexedAffinoidAtlas` over a
complete ultrametric normed field. It uses the actual affinoid spectra, bounded
restriction maps, embedded chart ranges and the atlas's net property. The field,
ambient space and index universes `u`, `v` and `w` remain independent.

`chartMemberOrderIso` identifies the chart order with the actual members of the
range family by sending a chart to its range. The atlas's injectivity of chart
ranges proves the inverse law; membership in the range family supplies the
inverse. Both orders are actual containment. Reindexing the published net
member colimit by this categorical equivalence gives
`chartRangeDiagramCoconeIsColimit` for the chart range diagram and its actual
inclusion cocone, with vertex the original space.

`liftedChartRangeCoconeIsColimit` uses Mathlib's colimit preservation by the
universe lift functor. The lifted range diagram lies in `TopCat` at `max u v`.
`chartSpectrumCoconeComparison` identifies its precomposition along the
published spectrum/range natural isomorphism with the actual spectrum cocone;
the vertex is unchanged and its legs are the lifted chart embeddings.
`chartSpectrumCoconeIsColimit` transports the universal property across this
natural isomorphism and the cocone comparison. Its diagram is the actual
spectrum functor applied to the opposite bounded affinoid restriction diagram,
then lifted from `u` by `v`; its vertex is the original space lifted from `v`
by `u`. No identification of those universes is assumed.
`chartSpectrumCocone_desc_chart` evaluates the resulting universal continuous
map at the image of a chart point and gives the corresponding supplied cocone
leg. `chartSpectrumCocone_hom_ext` proves that values at these chart points
determine any continuous map from the lifted space, by the colimit's uniqueness.

The source conventions are Berkovich, *Etale cohomology for non-Archimedean
analytic spaces* (1993), section 1.1, printed pp.13-14 (PDF pp.10-11), for nets
and Lemma 1.1.1(i), and Definition 1.2.3 with Remark 1.2.4(i), printed p.16
(PDF p.13), for actual chart algebras, spectrum coordinates and transitive
bounded restrictions. The registered original is
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The categorical transport and explicit universe lifts are derived consequences
of these already implemented atlas and net data.

This is a topological universal property of an already supplied atlas. It adds
no openness, Hausdorff, finiteness or intersection closure assumption. Algebra
section gluing, construction from abstract analytic gluing data, extended atlas
comparison, structure sheaves and analytic sites remain separate constructions.
