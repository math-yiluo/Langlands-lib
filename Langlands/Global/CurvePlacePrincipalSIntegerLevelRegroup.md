# Original upper level regrouping and the curve finite-level Weil homeomorphism

This derived construction completes the actual function-field finite-level
point-space comparison for the principal S-integer models in Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed page 10. It does not yet pass to the full adelic direct limit.

`indexMap` sends a pair consisting of an original lower level coordinate and
an original upper place above it to the corresponding upper level coordinate.
The upper exceptional set is the full preimage of the lower exceptional set,
so field coordinates map to field coordinates and integer coordinates to
integer coordinates. `indexInv` restricts an original upper place to recover
its lower coordinate. The two inverse identities prove `indexEquiv`.
The proof uses the existing equivalence between original place restriction
and equality of the original valuation-subring comap. Thus every original
upper place occurs exactly once.

`factorPointHomeomorph` verifies that each paired upper factor is exactly the
original upper level factor, with the same coefficient algebra and the same
`schemePointTopology`. After splitting into the field and integer cases,
this is the identity homeomorphism. `productPointHomeomorph` applies these
factor identities and reindexes the product by `indexEquiv`. Its component
formula retains the factor identity at each original paired index.

For a locally finite type, quasi-compact, quasi-separated upper S-integer
model Y equipped with a relative projective immersion,
`adelicLevelPointHomeomorph` constructs a homeomorphism from the actual lower
Weil model's points over the actual lower adelic level ring to Y's points
over the actual upper full-preimage adelic level ring. Both point spaces
carry their existing `curvePlaceLevelModelPointTopology`.

The proof composes the previously constructed actual lower level
homeomorphism to all original upper factors, the regrouping above, the
factorwise original base-change point homeomorphisms, and the inverse of the
proved actual upper level-model coordinate homeomorphism. The latter uses
the given upper model's quasi-compactness and quasi-separatedness. All local
rings and topologies are the original ones. No quasi-compactness of the
constructed lower Weil scheme is assumed.

`adelicLevelPointHomeomorph_coordinates` proves that applying the original
upper level-model coordinate map to the resulting point gives precisely the
base changes of the regrouped original local Weil components. The proof is
the inverse identity for the upper coordinate homeomorphism. Combined with
`productPointHomeomorph_apply` and the previously proved
`levelPointHomeomorph_component`, it identifies every component with the
original local Weil counit after the literal original lower level
projection.

All fields share an arbitrary universe. The constants are finite, the lower
field has its original function-field presentation and is finite over the
specified parameter subfield, the chart denominator is nonzero, and the
original upper extension is finite with compatible constant-field structures.
No separability is required. The lower exceptional levels are the previously
proved cofinal principal family. This proves the finite-level comparison for
the stated actual upper models; actual original-model existence and
generic-fiber identifications are proved separately. Number-field level
assembly, compatibility as levels enlarge and the full adelic Weil
homeomorphism remain host obligations.
