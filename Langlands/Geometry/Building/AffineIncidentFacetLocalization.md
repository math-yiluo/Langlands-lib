# Localizing incident affine facets at the roots through a point

Let `A` be an affine torsor over a real vector space `V`, with an arbitrary set
`Ψ` of real affine functionals. The universes of `V` and `A` are independent.
Fix `x : A`. The existing `vanishingRoots Ψ x` consists of the members of `Ψ`
that vanish at `x`. All facets and their combinatorial closures in this module
use the original sign definitions from `AffineRootSystem`.

`IncidentAffineFacet Ψ x` consists of the actual subsets `F` of `A` satisfying
`IsFaceOf Ψ (facet Ψ x) F`: the full facets whose combinatorial closures contain
the facet of `x`, including that facet itself. No topology on the torsor,
finite dimension, reducedness, essentiality, or nonemptiness of the root set
is assumed in the general construction.

For such a full facet, `incidentFacetLocalization` is its containing facet for
`vanishingRoots Ψ x`. Its definition chooses an original facet representative;
`incidentFacetLocalization_val_eq` proves that any point of the full facet gives
the same localized facet. `subset_incidentFacetLocalization` proves containment,
and `incidentFacetLocalization_eq_iff_subset` proves uniqueness among all
localized facets. The map is injective without a finiteness hypothesis.

The only extra premise for surjectivity and
`incidentFacetLocalizationOrderIso` is

```text
for every y : A, segmentRoots Ψ x y is finite.
```

Here `segmentRoots` consists of roots `ψ ∈ Ψ` with `ψ x * ψ y ≤ 0`.
Both orders in the displayed `OrderIso` are supplied explicitly by the existing
`IsFaceOf` predicates on the underlying facets. They are not defined by
transport through the new equivalence; no global order instance is introduced.
`isFaceOf_incidentFacetLocalization_iff` proves preservation and reflection of
these original predicates. The forward map is recorded by
`incidentFacetLocalizationOrderIso_apply`.

The specialization
`IsAffineRootSystemWithRankZero.incidentFacetLocalizationOrderIso` obtains
finite separation from the existing `finite_segment_roots` theorem. It applies
to the Library's corrected affine root-system axioms, including the empty
rank-zero case.

The proof first observes that any root nonvanishing at `x` has the same sign on
every facet incident above `x`. Thus restricting to `vanishingRoots Ψ x`
preserves and reflects both equality of facet sign patterns and membership in
combinatorial closed facets. These are
`facetRel_iff_vanishingRoots_of_incident` and
`mem_facetClosure_iff_vanishingRoots_of_incident`.

For surjectivity, `exists_incident_point_with_localized_facet` starts with an
arbitrary `y` and chooses a sufficiently short positive segment parameter
`0 < t < 1` from `x` toward `y`. Among roots nonvanishing at `x`, those with
nonpositive endpoint product form a finite set; scalar continuity keeps all
their signs equal to the sign at `x` for sufficiently small `t`. The remaining
nonvanishing roots have endpoints of the same strict sign, so retain that sign
along the segment. Roots vanishing at `x` have value `t * ψ y`, hence the sign
at `y`. The resulting point `z` satisfies `x ∈ facetClosure Ψ z` and lies in
the localized facet of `y`. Only real scalar continuity is used; no torsor
topology is needed. This existence result requires finiteness of the separating
roots for the individual segment, rather than for all endpoints at once.

Finally, the existing `isFaceOf_facet_iff_facetClosure_subset` and
`facetClosure_subset_facetClosure_iff` reduce the original face predicates to
point membership in closures. The restriction comparison above proves the
order equivalence. `Equiv.ofBijective` packages the injectivity and short-segment
surjectivity, and the original face comparison supplies the `OrderIso` field.

The source is Kaletha–Prasad, *Corrections and additions in the book
Bruhat–Tits theory: a new approach*, version 1 November 2024, replacement for
Proposition 1.3.35(8)(i), PDF pages 4–6. That correction identifies full facets
incident above a fixed facet with facets of the hyperplanes containing it,
and states preservation of the original orders. The present construction is
a derived version for the Library's affine-functional sign definitions: it
replaces the source's local-finiteness neighborhood argument by the explicit
finite-segment argument above. Roots through `x` are exactly the roots
vanishing on `facet Ψ x`, by the existing `vanishingRoots_eq_of_facetRel`.

This module supplies only the apartment localization in part (i). It does not
assert the derivative comparison in part (ii), classification by all parabolic
root subsets in part (iii), or any special-fibre group-scheme parabolic
correspondence. Those remain separate obligations for the unramified
facet-model parabolic-order theorem.
