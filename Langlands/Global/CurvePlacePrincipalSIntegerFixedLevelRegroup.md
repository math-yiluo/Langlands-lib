# Enlarged curve levels of the original principal integral models

This derived construction continues Conrad, *Weil and Grothendieck approaches
to adelic points* (2011), Example 4.2, printed pp.9–10. The constants k are
finite. The lower field K has the specified rational-function presentation,
with its compatible k-action, and is finite over the parameter subfield
k(s). The nonzero chart denominator t fixes the original principal finite
support S. The upper extension L/K is finite with compatible k-actions;
separability is not required. For every finite support T containing S,
retain the original rings A of lower S-integers and B of upper integers
away from the full preimage of S.

`upperLevel` is the full preimage of T, with its proved containment of the
original upper support. `indexMap` regroups each lower field or integer
coordinate and upper place above it as an original upper level coordinate.
`indexInv` restricts an upper place to its unique lower coordinate.
The inverse identities prove `indexEquiv`; they use the existing equivalence
between place restriction and equality of valuation-subring comaps.
Thus every original upper place occurs exactly once at the enlarged level.

`factorPointHomeomorph` preserves the actual upper completed field or
completed integer ring, the original fixed B-action and its original
`schemePointTopology`. In both branches algebra extensionality identifies
the coefficient actions, after which the map is the identity homeomorphism.
`productPointHomeomorph` takes their product and reindexes it by
`indexEquiv`. Its application theorem gives its exact value.

For every quasi-compact, quasi-separated B-scheme Y,
`upperPointHomeomorph` identifies its actual enlarged-level points with the
product of its original upper local point spaces. Its source carries the
independently defined `curvePlaceFixedModelStageTopology`, and the factors
carry `schemePointTopology`. The proof composes the arithmetic fixed-model
stage homeomorphism with the actual product-point bijection. Injectivity
uses quasi-separatedness; surjectivity uses quasi-compactness and the actual
local coefficient rings. The existing inducing coordinate theorem supplies
the topology comparison. `upperPointHomeomorph_coordinate` identifies each
coordinate with the literal upper enlarged-level projection on spectra.

Suppose additionally that Y is locally of finite type and has a specified
relative immersion into a finite-dimensional projective space over B.
`adelicLevelPointHomeomorph` compares actual points of the original integral
Weil model over the lower T-level with actual points of the original Y over
the upper full-preimage T-level. Both carry their existing fixed-model
stage topologies. It composes the proved fixed-base local Weil homeomorphism,
the product regrouping above and the inverse upper coordinate homeomorphism.
This assembly assumes no finiteness or separation condition on the lower
Weil scheme.

`adelicLevelPointHomeomorph_coordinates` identifies the entire upper
coordinate family with the regrouped original local Weil components.
`adelicLevelPointHomeomorph_coordinate_left` gives the same equality after
each literal upper projection. Combined with the imported local component
theorem, this preserves the original local Weil counit after the literal
lower projection. The proof uses the upper inverse identity and the exact
regrouping and projection laws.

All fields share an arbitrary universe. Only the initial support is
principal: the variable enlarged support T can be any finite support above
it. Compatibility with support inclusions, the cofinal passage to full
adelic points and the original generic-fiber/spread comparison remain
host obligations.
