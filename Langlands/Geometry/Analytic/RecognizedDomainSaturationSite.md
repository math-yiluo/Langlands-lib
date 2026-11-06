# Saturation after full recognition preserves the domain site

Author: Worker 36.

This module proves a further closure property of the constructed domain site.
Starting with an actual indexed affinoid atlas `a`, put
`R = a.saturatedAtlas`, `F = a.fullRecognitionAtlas = R.recognitionAtlas`
and `B = F.saturatedAtlas`. The actual original-chart domains of `B` are
exactly those of `R`, on the same literal subsets of the ambient space.
The module constructs their order and category equivalences, proves
preservation and reflection of all covering sieves and arbitrarily indexed
generated covering families, and constructs an equivalence of sheaf
categories with arbitrary categorical coefficients.

The source conventions are Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), §1.1, printed pp.13–14 / PDF pp.10–11, for contained
members and finite quasinet neighborhoods; Proposition 1.2.13(iii), printed
p.21 / PDF p.18, for the motivation of iteration of affinoid recognition;
Definition 1.3.1 and its following paragraph, printed p.23 / PDF p.20,
for analytic-domain subsets and their contained-chart atlases; and the
G-topology paragraph, printed p.25 / PDF p.22, for quasinet coverings.
Registered source `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read; no source-specific errata file was found
in the available project and Library locations.

The result is derived from the actual finite original local-domain
refinement in `RecognizedDomainFiniteRefinement` and the proved
refinement invariance of the quasinet domain site. It is not claimed as
a separately numbered source theorem or as a proof of maximal affinoid
recognition or its idempotence.

`isOriginalChartDomain_of_finite_chart_cover` first proves a reusable
topological lemma. Suppose finitely many actual chart ranges have union
`S`, and the induced space `S` is Hausdorff. Each chart range, pulled back
to `S`, is compact and hence closed there. The existing finite closed-cover
quasinet lemma applies to this finite family, considered inside the
restricted family of all original charts contained in `S`. Its finite
neighborhood witnesses are obtained by excluding the union of cover
members that do not contain the point. No global Hausdorff premise or
arbitrary compact-cover extraction appears.

For a recognized chart `V` and a full domain `D` in its actual algebra,
`RecognizedSubset.domainLocusHomeomorph` uses the proved embedding and
range formula for the actual composite spectrum map to identify
`BanachSpectrum D.algebra` with `V.domainLocus D`. Its value formula
recovers exactly the original composite map after forgetting the subtype.
This supplies Hausdorffness of that literal subset without an ambient
separation assumption.

For `V : R.RecognizedSubset`, the finite refinement already constructs
`a.fullRecognitionDomainPiece V D i : LocalDomain a`, with union exactly
`V.domainLocus D`. `fullRecognitionDomainPieceIndex` uses the literal
locus and this actual full-domain witness as an index of `R`.
`range_fullRecognitionDomainPieceIndex` identifies the constructed
saturated chart's range with precisely that piece locus. Its chosen
saturated chart algebra need not be definitionally the refinement's
quotient algebra; this unit uses its literal range, while the refinement
module retains the quotient algebras and bounded maps explicitly.

`fullRecognitionDomainLocus_isOriginalChartDomain` applies the finite
chart-cover lemma to these constructed indices. Consequently
`fullRecognitionLocalDomain_isOriginalChartDomain` proves that every
actual local full domain in `F` is an original-chart domain for `R`.
This condition is proved for arbitrary supplied full domains, not
assumed as an output-geometric premise.

Each chart in `B` is given by the actual chosen local full-domain
representative in `F`. The preceding result and its exact locus formula
therefore give
`chartFamily_locallyRefines_saturatedFullRecognitionAtlas`.
Conversely, each chart range of `R` occurs as the range of its original
recognized copy in `F`, and hence as a chart range of `B`.
`chartFamily_subset_saturatedFullRecognitionAtlas` proves this inclusion,
and `saturatedFullRecognitionAtlas_locallyRefines_chartFamily` gives the
reverse local refinement.

The two proved refinements give
`isOriginalChartDomain_saturatedFullRecognitionAtlas_iff` on every literal
ambient subset. Combining this with the existing recognition-domain
comparison gives
`isOriginalChartDomain_fullRecognitionAtlas_saturation_iff`: saturation
after full recognition also preserves the domain subsets of `F` itself.
Neither statement identifies these domains with the original-chart
domains of the unsaturated input `a`.

`saturatedFullRecognitionDomainOrderIso` and
`saturatedFullRecognitionDomainEquivalence` specialize the existing
refinement constructions to `R` and `B`. Both directions retain each
literal subset and change only its proved domain condition. These objects
still carry their actual constructed contained-chart subspace atlases.
The module does not identify those presentations as raw strong maps or
compare their bounded coefficient restrictions.

`sieveFamily_functorPullback_saturatedFullRecognition` states equality of
the entire families of source subsets in an arbitrary sieve and its
pullback. `functorPullback_mem_saturatedFullRecognitionDomainTopology_iff`
therefore preserves and reflects every quasinet-covering sieve.
`ofArrows_saturatedFullRecognition_mem_iff` gives the corresponding
criterion for generated families with arbitrary index universe.
These results specialize the already proved generic refinement theorems.

`saturatedFullRecognitionDomainSheafEquivalence` restricts along the
inverse site equivalence for any coefficient category. Its object-value
and morphism-component formulas evaluate at the same literal subset with
the transported domain proof. The coefficient object and hom universes
are independent; no sheafification, limits or abelian hypothesis is needed.

The field, ambient-space and original-index universes remain independent.
The field is complete and ultrametric, including trivial valuations.
Empty domains, empty finite covers, zero algebras and nonreduced algebras
are allowed. The unit proves domain-site invariance under the specified
additional saturation. It does not establish equality of maximal affinoid
chart families, recognition of the new domains' entire section algebras,
structure-sheaf comparison, unrestricted analytic factorization or the
analytic étale site. No special-intersection or closed-ideal-effectiveness
theorem is assumed.
