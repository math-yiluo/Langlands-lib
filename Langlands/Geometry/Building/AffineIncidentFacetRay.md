# Prescribed positive rays in incident affine facets

This internally derived helper works with an arbitrary real affine torsor and
the original affine-root facets. It strengthens the finite-segment construction
in `AffineIncidentFacetLocalization` by retaining the prescribed direction and
the positive scalar.

For endpoints `x` and `y`, assume only finiteness of `segmentRoots Ψ x y`.
`eventually_lineMap_incident_with_localized_facet` shows that every sufficiently
small positive segment parameter gives a point whose full facet is incident
above the facet of `x` and whose facet for roots through `x` agrees with that of
`y`. No topology on the affine torsor is required: continuity is used only for
the real-valued affine functions of the scalar parameter.

The proof treats the finite set of roots that are nonzero at `x` and separate
the endpoints. Their signs remain constant near scalar zero by continuity.
Other roots nonzero at `x` have same-sign endpoint values, so every parameter
strictly between zero and one preserves their signs. Roots through `x` evaluate
as the positive scalar times their value at `y`, preserving their localized
signs.

`mem_incidentFacetDerivative_iff` translates membership in the actual derivative
facet back into membership in the localized facet. For an original incident full
facet `F` and any vector `w` in `incidentFacetDerivative F`, assume finite
separation on the single segment from `x` to `w +ᵥ x`.
`eventually_pos_smul_vadd_mem_incidentFacet` proves that `(t • w) +ᵥ x` lies in
the original `F` for every sufficiently small positive `t`. The segment result
gives an incident full facet with the same localization as `F`; injectivity of
the existing localization identifies it with `F`.

`exists_pos_smul_vadd_mem_incidentFacet` chooses such a parameter with
`0 < t < 1`. `incidentFacetRayParameter` and its specification expose a chosen
real scalar satisfying those inequalities and the original-facet membership.
The vector may be zero, and no positive-rank or chamber hypothesis is imposed.

These are internal consequences of full sign facets, finite segment separation
and the previously constructed localization; no new original-source claim is
made. There is no assertion about integral models or special-fibre parabolics.
