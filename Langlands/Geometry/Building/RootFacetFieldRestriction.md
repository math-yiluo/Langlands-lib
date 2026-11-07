# Ordinary walls and facets under actual field restriction

This internal construction continues `RootAffineFieldRestriction` for the
literal base change of a supplied original split torus and inclusion.
Both fields have the same arbitrary universe. The original group is
smooth and affine, the inclusion is monomorphic, original opposite
factor pairs are supplied, and the upstairs real unit character has
nonzero restriction on some original unit. An upstairs `KPApartmentData`
is supplied. Its original apartment is exactly the previously constructed
`fieldRestrict`.

The previous extended-root inclusion does not alone identify ordinary
roots: their definition also uses a product with the doubled-root group.
This unit obtains ordinary walls and facet refinement using the existing
doubling theorem.

`no_quadruple_root_fieldExtend` proves that the actual upstairs relative
root set has no quadruple roots. Every upstairs character comes from the
original split torus. Reflect membership of that character and its
quadruple using actual root base change. Original opposite factor pairs
already exclude quadruple roots, so the upstairs quadruple cannot occur.
No opposite-pair or apartment-axiom assumption on the extension is added.

`fieldExtendedOrdinaryAffineRoot` constructs an ordinary upstairs root for
every original extended root. Extend the original functional using actual
apartment restriction, apply the proved extended-root inclusion, and then
apply `ordinaryAffineRootForExtended` with the proved absence of quadruple
roots. The selected root is the extended functional itself or twice that
functional, as stated by
`fieldExtendedOrdinaryAffineRoot_eq_or_eq_two_smul`.

The two choices have identical signs and identical hyperplanes. Thus
`fieldExtendedOrdinaryAffineRoot_sign` gives exactly the sign of the
original functional at the restricted point, and
`fieldExtendedOrdinaryAffineRoot_hyperplane` identifies the full upstairs
ordinary wall with the affine inverse image of the original extended
wall. These are actual ordinary roots of the supplied upstairs apartment.

`facetRel_affineRoots_fieldRestrict_extended` evaluates an upstairs
ordinary-root sign relation on each selected root. The resulting signs
agree for every original extended root. Original ordinary roots are
extended roots, so `facetRel_affineRoots_fieldRestrict` and
`image_facet_affineRoots_fieldRestrict_subset` give refinement for the
ordinary-root facets used in the building construction.

The same evaluation argument applies to the weak sign conditions defining
facet closures. It proves
`mem_facetClosure_affineRoots_fieldRestrict_extended` and
`image_facetClosure_affineRoots_fieldRestrict_subset`. Finally,
`isVertex_of_fieldRestrictPoint` uses ordinary facet refinement and the
proved injectivity of apartment restriction: every point in the upstairs
facet of a lift of an original vertex restricts to that same original
vertex, and therefore equals the lift.

The provenance is internal, from actual root membership base change, the
opposite-pair integrality bound, the existing root-doubling proof,
extended-root field restriction, and the existing sign definitions of
facets, closures and vertices. This unit supplies no initial apartment or
vertex. It does not prove that each original ordinary functional itself
extends to an ordinary root, identify the complete arrangements or
facets, compare proper enlarged split tori, construct a Galois fixed
locus, or prove building axioms. The supplied-model special point,
stabilizer equality, unique fixation and full `BuildingComparisonStatement`
remain open.
