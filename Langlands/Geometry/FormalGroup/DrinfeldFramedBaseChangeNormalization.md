# Actual normalized framing square over a varying Nilp base

This internal unit proves the test-chart equation for the actual normalized
framing of the constructed Nilp-base extension. It uses exactly the fixed-frame
and target test-chart comparisons of `DrinfeldFramedBaseChangeCharts`, with
no new original-source or representability assertion.

`baseChangeOriginalGlobalChartIso` transports the original global normalization
to the new scalar structure on the same test ring.
`baseChangeOriginalChartFraming` is its rationalized inverse followed by the
same transported original rational framing chart. No additional framing is
chosen.

`chartFraming_baseChange` states an equality of complete actual full-order
quasi-isogenies. Following the new normalized framing with the actual target
test comparison equals following the actual fixed-frame test comparison with
this transported original normalized framing. The proof evaluates the actual
isomorphism-transport construction and supplied-target coefficient extension
on charts. It then uses associativity and the actual inverse equations to
cancel the target quotient, target coefficient and original global
normalization comparisons. The cancellation is proved separately as
`normalization_transport` for actual full-order quasi-isogenies on one finite
coordinate type, which applies to these fixed-dimension special atlases.
The specialized proof composes the exact chart and rationalization equations
by congruence; it does not search through expanded frame constructions. The two rationalization lemmas preserve composition
and inversion of the actual integral full-order isomorphisms.

`baseChangeChartFramingSquare` packages exactly these four actual rational maps
and the proved equation as the existing full-order quasi-isogeny commuting
square structure. Equality of point evaluations is not used to reconstruct
formal maps or tensors.

The parameters retain the local field, finite-dimensional central division
algebra, embedded field, coefficient and residue fields, fixed height-certified
frame and Nilp objects in universes `{v,u}`. Covers may be infinite and quotient
scalar maps may merge generators. Independence of the fixed-frame test
comparison from the target chart and preservation of original framed
comparison squares remain further constructions.
