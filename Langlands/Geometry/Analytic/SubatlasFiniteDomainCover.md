# Actual finite full-domain refinements through a locally refining subatlas

Author: Worker 36.

The module constructs a finite selected-chart cover of every original
affinoid chart and restricts it to every actual full affinoid domain in
that chart. Each resulting quotient algebra is simultaneously a full
domain over the given domain algebra and an actual local domain of the
selected atlas. Both presentations have the same ambient map.

## Source and provenance

This is derived infrastructure for Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Proposition 1.2.13(i), printed
p.21 / PDF p.18. The original argument compares recognition for equivalent
nets by finite subordinate coverings of original chart domains. The Lean
module constructs a finite refinement through the stronger explicit
hypothesis that the selected chart family locally refines the original
one. It does not claim to prove all of that proposition.

The registered source is `berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The cover extraction uses the published `AtlasTopology.LocallyRefines`
compactness theorem. The algebraic constructions use the original
atlas's bounded restrictions, full-domain intersections and relative
domain universal properties.

## Finite selected charts

For an actual indexed affinoid atlas `a`, a selection predicate `P` and
an original index `parent`, `SelectedChartCover P parent` consists of a
natural number, that many indices satisfying `P`, and the equality
between the union of their chart ranges and the parent's chart range.
Repeated indices and empty covers are permitted when the equality allows
them. The record contains no comparison algebras or desired output atlas.

`selectedChartCover P hP parent` constructs this data from
`hP : a.IsLocallyRefiningSelection P`. It restricts the local refinement
to the singleton parent family and applies compactness of the parent's
embedded Banach spectrum. Classical choice selects the finite witness;
a finite-type equivalence reindexes it by `Fin`.

`subset_parent` proves every chosen range is contained in the parent.
`component i` is exactly the original `restrictionDomain` for that
inclusion. Its algebra is the unchanged selected original chart algebra.
`component_over_ambient` is the original bounded restriction's chart
compatibility. `domainCover` packages these actual full domains into a
finite cover of the whole parent spectrum. Its maps are the original
bounded restrictions, and its covering proof pulls the chosen ambient
range equality back to each spectrum point.

## Refining an arbitrary full domain

For every `U : Domain K (a.algebra parent)`, `algebraCover U` intersects
`U` with every component in the parent algebra, then expresses the
intersection relative to `U`. These relative domains cover the whole
spectrum of `U.algebra`: a point maps into `U` and into one component,
so lies in the corresponding relative intersection domain. The arrows
are the actual intersection restrictions.

`selectedLocalPiece hP U i` expresses the very same intersection
relative to its selected component and uses that selected chart as its
parent in `a.subatlas P hP`. Both presentations retain the identical
intersection quotient algebra; `selectedLocalPiece_algebra` records
this definitional equality.

`selectedLocalPiece_over_ambient` proves that the selected local-domain
map is the parent chart composed with `U`'s spectrum map and the
corresponding `algebraCover` component map. The proof uses compatibility
of the original component restriction and the two intersection
structural maps over the original parent.

`selectedLocalPiece_locus` identifies each selected piece's locus with
the intersection of `a.chart parent '' U.locus` and its selected chart
range. The proof uses the relative domain's exact image formula, then
the intersection's defining locus. `selectedLocalPiece_covers` combines
these intersection formulas with the finite selected-chart cover to
give equality of their union with `a.chart parent '' U.locus`.

## Hypotheses and scope

The field is complete and nonarchimedean, with explicit `NormedField`,
`IsUltrametricDist` and `CompleteSpace` instances. The field, ambient
space and chart index have independent universes. The ambient space
has its given topology; global Hausdorffness is not required. Compactness
is used only for the embedded original affinoid spectrum. Neither
reducedness nor nontriviality of the valuation is assumed.

The construction proves a finite full-domain refinement, its exact
ambient compatibility and its coverage. It does not yet construct
recognition comparisons, compatible overlap diagrams, equivalences of
the recognized categories for arbitrary equivalent nets, maximal
atlases, or analytic etale sites.
