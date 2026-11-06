# Domain sites of the constructed recognition atlas

Author: Worker 36.

This module proves that the constructed recognition extension has exactly the
same original-chart domains and quasinet domain site as its supplied atlas.
The comparison preserves literal subsets, their inclusion order, every
covering sieve and arbitrarily indexed generated covering families. It
constructs an equivalence of sheaf categories for any coefficient category.

The source conventions are Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), §1.1, printed pp.13–14 / PDF pp.10–11, for contained
members and quasinets; Proposition 1.2.13(ii), printed p.21 / PDF p.18, for
the recognition extension; Definition 1.3.1, printed p.23 / PDF p.20, for
the relative neighborhood condition on domains; and the G-topology paragraph,
printed p.25 / PDF p.22, for quasinet coverings. Registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read for this unit; no source-specific errata
file was found in the available project and Library locations.

The result is derived from the constructed recognition atlas and the
published mutual-local-refinement comparison. It is not asserted as a
separately numbered source theorem or as a proof of all maximal-atlas
assertions in Proposition 1.2.13.

Every recognized subset has a finite cover by original charts and a
Hausdorff locus. The imported finite closed-cover argument supplies a
quasinet of contained original charts on that locus. The bridge
`RecognizedSubset.isOriginalChartDomain` expresses this as the original
domain condition. `chartFamily_locallyRefines_recognitionAtlas` transfers
it to the exact ranges of the constructed recognition charts.
Conversely, `chartFamily_subset_recognitionAtlas` uses the constructed
original recognition index to include every original chart range.
Enlargement of the refining family gives
`recognitionAtlas_locallyRefines_chartFamily`. No arbitrary compact-cover
extraction or global Hausdorff assumption is used.

The two finite relative local refinements give
`isOriginalChartDomain_recognitionAtlas_iff`,
`recognitionDomainOrderIso` and `recognitionDomainEquivalence` by the
existing constructions in `OriginalDomainRefinement`. Both directions
retain exactly the supplied subset and change its domain proof.
The domains still have their actual subspace atlases from the imported
domain construction.

`sieveFamily_functorPullback_recognition` identifies the whole family of
source subsets of an arbitrary sieve with that of its pullback.
`functorPullback_mem_recognitionDomainTopology_iff` consequently preserves
and reflects the full finite relative neighborhood covering condition.
`ofArrows_recognition_mem_iff` gives the corresponding criterion for
generated families, with an arbitrary index universe. These declarations
specialize the existing generic refinement theorems.

`recognitionDomainSheafEquivalence` specializes the constructed refinement
equivalence of sheaf categories, obtained by restriction along the inverse
site equivalence. The value and morphism-component formulas state that
the same sheaf data are evaluated at the same literal subset, with its
domain proof transported back. The coefficient category and its hom
universe are independent; no sheafification or limits premise is needed.

Finally, the `fullRecognition` declarations apply this result to
`a.saturatedAtlas`. They compare that enlarged full local-domain atlas
with `a.fullRecognitionAtlas`. They do not identify the original-chart
domains of the input `a` with all those of `a.saturatedAtlas`.
The coefficient field is complete and ultrametric, with no nontrivial
valuation assumption. Empty domains, empty covering families, zero
algebras and nonreduced algebras remain allowed.

This unit concerns the existing actual domain inclusion categories and
their quasinet sites. It does not identify structure sheaves or their
bounded restrictions under this comparison, construct the analytic étale
site, prove recognition closure or idempotence, or establish recognition
invariance under arbitrary equivalent full nets. The special-intersection
statement and closed-ideal effectiveness are not assumed.
