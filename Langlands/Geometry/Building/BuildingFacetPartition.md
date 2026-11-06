# The partition of the actual valuation quotient by building facets

This internal construction concerns supplied `ValuationBuildingData G` over
any nonarchimedean local field, at every universe `u`. Under the full
`B.SatisfiesApartmentAxioms` predicate, the original building facets partition
the original quotient points. The full predicate retains AS5. No opposite
factor pairs, apartment-map injectivity, building axiom, normalizer-stabilizer
equality, polysimplicial realization or metric is assumed in this deduction.

Two building facets containing a common point coincide. Therefore every point
lies in exactly one existing `BuildingFacet B`, and distinct facets are
disjoint. The definition `buildingFacetAt` chooses a containing facet using
the unconditional existence of a facet through any quotient point; uniqueness
and all its subsequent characterizations use the displayed apartment axioms.
In any translated apartment chart its underlying subset is exactly the image
of the affine facet through those coordinates. It respects the original
rational-point action, as an equality of subsets of the same quotient.

`buildingFacetSetoid` is the kernel equivalence relation of that chosen map.
Under the apartment axioms, its equivalence classes are exactly the original
building facets. The entry `buildingFacetQuotientEquiv` identifies this quotient
of the original point carrier with the existing `BuildingFacet B` type. This
quotient classifies facets and is distinct from the original valuation quotient
that supplies the points; it does not replace that point carrier.

## Implemented proof and provenance

For affine facets, equality follows immediately from the existing sign-facet
equivalence relation when a point belongs to both. For building facets written
as `g • apartmentMap '' Fa` and `h • apartmentMap '' Fb`, a common point gives
coordinates `a ∈ Fa` and `b ∈ Fb`. Apply the `ApartmentFacetConstruction` theorem
`exists_normalizer_eq_on_translated_facet` to `h⁻¹g`. It gives a
single normalizer element `n` with `n • a = b` and
`(h⁻¹g) • apartmentMap y = apartmentMap (n • y)` for all `y ∈ Fa`.
The same module proves `n • Fa` is an affine facet using AS5, so its common
point with `Fb` implies `n • Fa = Fb`. Multiplying the displayed equality by
`h` identifies the entire two original building facets.

The containing-facet map, its uniqueness, its chart formula, its equivariance
and its surjectivity then follow from this equality theorem and unconditional
facet existence. Mathlib's kernel-quotient equivalence for a surjective
function gives the final data equivalence. These are internal deductions from
`ApartmentFacetConstruction`, `CommonApartmentConstruction`, the original
`AffineRootSystem` and `ValuationBuildingData` facet definitions, and Mathlib's
setoid API. No independent external source assertion is introduced.

This gives part of the facet structure needed for the parent construction. It
does not construct actual valuation data, prove their apartment axioms, give
a polysimplicial realization, establish building or face-incidence axioms, or
prove the full `RootValuationBuildingConstructionStatement`.
