# Actual curve adelic-level Weil points and all original upper factors

This derived arithmetic instantiation supplies the lower-level product
comparison in Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), Example 4.2, printed page 10. It uses the actual cofinal principal
exceptional sets and the actual upper S-integer ring for the full preimage
under original place restriction.

`lowerPlace` sends an actual lower adelic-level coordinate to its original
curve place. `Above` is the existing subtype of **all** original upper
places above it. `upperFactor` is the original upper completed field for a
lower coordinate inside S, and the original upper completed valuation ring
for one outside S. Thus the product indices retain the actual original lower
and upper places, with no auxiliary abstract place system.

The scoped ring, topology and algebra instances are the existing structures
on these actual local rings, selected according to the lower coordinate.
Outside S the upper coefficient map is the proved original upper S-integer
inclusion in its completed valuation ring. The outside membership needed
there is the lower coordinate's existing subtype property. Every upper
factor is finite projective over the corresponding lower local ring and has
its original finite-module topology: for fields use the original finite
completion extension and a basis over the lower field; for integers use
`CurvePlaceIntegralTopology`. The field topology comparison uses the
nontrivial norm from the original lower discrete valuation.

`tensorEquiv` selects the proved actual S-integer completed-field tensor
inside S and the proved actual S-integer completed-integer tensor outside S.
Its right coefficient formula is the original upper coefficient algebra
map in both cases. The scalar actions on the lower factors are the existing
original adelic diagonal/projection actions from `AdelicLevelModelPoints`;
the typed equivalences and coefficient formulas use exactly these actions.

For a locally finite type, quasi-compact, quasi-separated upper S-integer
model Y equipped with a relative projective immersion,
`levelPointHomeomorph` constructs a homeomorphism from points of the actual
lower Weil model over the actual lower adelic level ring to the product of
Y's points at all the `upperFactor` rings. The lower space has the existing
`curvePlaceLevelModelPointTopology`; the upper factors have the existing
`schemePointTopology` and their product topology.

The proof first applies the original lower level ring's coefficient
equivalence to the product of its local factors. The previously proved
equality of level topologies makes this change-of-coefficients point
equivalence inducing, hence a homeomorphism. Composing with
`productTensorWeilPointHomeomorph` and the actual arithmetic data above gives
the result. The projective immersion supplies separatedness and finite
affine neighborhoods of Y. No quasi-compactness of the constructed Weil
scheme is assumed.

`levelPointHomeomorph_component` proves that each upper component is the
original local Weil counit map after the literal original projection of the
lower adelic level. Its proof identifies coordinate restriction after the
level coefficient equivalence with that original projection, then applies
the general product-point local identity.

All fields have an arbitrary common universe. The constants are finite, the
lower field has its original function-field presentation and is finite over
the specified parameter subfield, the denominator is nonzero, and the
original upper extension is finite with compatible constant-field structures.
There is no separability hypothesis. The result covers the proved cofinal
principal exceptional levels. The upper product is indexed by a lower
coordinate together with an original upper place above it; identifying it
with the single upper full-preimage adelic-level point space, number-field
level assembly and the full adelic Weil comparison remain host obligations.
