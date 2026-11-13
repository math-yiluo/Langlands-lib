# Facets meeting the actual Galois fixed locus

The module uses the actual coefficient action on the supplied integer-valued
reduced building. `IsGaloisFixed` means fixed by every coefficient automorphism,
and `galoisFixedLocus` is that subset of the original quotient. A
`GaloisFacet` is an existing full building facet whose intersection with this
fixed subset is nonempty; `galoisFacetFixedPart` is exactly that intersection.
No new quotient or replacement full-facet predicate is introduced.

The parameters are arbitrary fields `K/k` in universe `u`, a commutative
`k`-group `T`, an affine `k`-group `G`, a map whose base change is monomorphic,
an integer-valued valuation of `K`, and a supplied KP apartment with
Galois-stable valuation class. Connected reductivity, maximal splitness,
centralizer data and full V6 compatibility are supplied. The existing
`integerBuildingData` construction only bundles these data. There is no
characteristic or local-field restriction and no assertion that all these
supplied data exist.

`GaloisFixedFacetIncidenceStatement` asserts that every coefficient-fixed point
belongs to exactly one fixed part, that the fixed-part map is injective, and
that each such upstairs facet is invariant. It also identifies the union of
all incident lower fixed parts with the intersection of the original
combinatorial closure and the fixed subset. Finally, the upstairs incidence
relation is equivalent to containment of one fixed part in that fixed closure.
`galoisFixedFacetIncidence` proves this entire assertion.

The proof is an internal deduction from `GaloisFacetAction`,
`IntegerBuildingFacetPartition` and `IntegerBuildingFacetClosure`. The unique
upstairs facet through a fixed point meets the fixed set by that same point.
Uniqueness of the upstairs full facet proves uniqueness of the fixed part.
If two fixed parts are equal, a point in their nonempty intersection identifies
their upstairs facets by the partition, proving injectivity. The actual
coefficient action preserves full facets and fixes the selected point, so the
same partition makes each entire upstairs facet invariant.

`GaloisFacetPrecedes` is exactly `IntegerValuationBuildingData.FacetPrecedes`
on the underlying full facets. `galoisFacetClosure` is defined as the union of
the fixed parts of all incident lower Galois facets. For the nontrivial
inclusion in the closure-intersection equality, take a fixed point in an
upstairs combinatorial closure. Its unique full containing facet is itself a
Galois facet; the original closure membership theorem makes this facet
incident below the upper one. The reverse inclusion follows directly from
upstairs incidence. One fixed point in a facet and an upper combinatorial
closure already determines the upstairs incidence, giving both the
nonempty-intersection and subset characterizations. The auxiliary
`galoisFacetClosure_subset_apartment` uses the original closed-facet apartment
containment to put this fixed closure in every translated apartment containing
the entire upstairs facet.

All closures here are combinatorial unions, without any topology asserted on
the quotient. Only the direction from meeting the fixed set to invariance is
proved; no converse is needed or asserted. The module does not prove the
existence of maximal Galois facets, a descended integral-model family, a
residue-parabolic correspondence, a torus lift or a special apartment through
a prescribed point. `UnramifiedFixedPointSplitTorusStatement` remains open.
