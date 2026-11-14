# Coefficient transport and invariant incident facets

This internal unit works with the actual coefficient-stable integer-valued KP
apartment data over a field extension `K/k`, in arbitrary universe `u` and either
characteristic. The connected reductivity, maximal split torus, centralizer,
coefficient stability and full V6 premises are the same supplied inputs as in
`GaloisFacetCentroids` and `GaloisMaximalFacets`. No local-field structure on `K`
is assumed.

The coefficient action preserves and reflects the common-apartment incidence
relation on the original full facets. The proof first uses the published inverse
coefficient root-functional transport to put the coefficient affine map in the
actual root stabilizer. Its affine images preserve faces. Applying the actual
semilinearity identity to both charts transports a common-apartment witness for
incidence. The inverse coefficient map reflects it. Since a combinatorial facet
closure is the union of its incident lower full facets, its entire image is the
closure of the image facet.

For a Gamma-facet `E`, already proved invariant because it meets the actual fixed
locus, `galoisIncidentFacetAction` restricts the same coefficient permutations to
`IntegerValuationBuildingData.IncidentFacets E.val`. It changes neither the full
facets nor their incidence. A point of this incident-facet set is fixed by all
these permutations exactly when its underlying full-facet subset is invariant.

With the explicit affine-root-system premise, an invariant incident facet has
its canonical centroid in the coefficient-fixed locus, by the published
`isGaloisFacet_iff_invariant`. It therefore belongs to the original Gamma-facet
set, so maximality of `E` makes that facet equal to `E`. Conversely, that equality
criterion applied to Gamma-facets gives maximality. The integer affine-root-system
proof `IntegerValuationBuildingData.isAffineRootSystemWithRankZero_affineRoots`
discharges the affine-root-system premise from an order-one field unit. This gives
`isMaximalGaloisFacet_iff_no_other_fixed_incident`. Combining the invariant-facet
criterion with the published maximal-Gamma-facet existence theorem puts each
actual fixed building point in the combinatorial fixed closure of such a facet.

`GaloisIncidentFacetsStatement` collects coefficient transport of incidence and
closures and the maximality criterion under an order-one-unit premise.
`galoisIncidentFacets` proves it. The normalization premise is explicit; the
published `MaximalUnramified.exists_order_eq_one` supplies it over the actual
maximal unramified field. This unit constructs no residue-parabolic
correspondence, integral model or torus lift and does not prove the prescribed
fixed-point split-torus theorem. Its role is the geometric maximality step needed
once a rational residue parabolic produces an invariant incident full facet.
