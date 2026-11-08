# Strictly Henselian classification for the original unramified model

This internal construction works in every universe `u`, for an arbitrary
nonarchimedean local field `F`, an actual connected reductive group `G/F`, and
the original supplied integral model `M`. The only special-fibre hypothesis
on `M` is connected reductivity of its actual full residue-field pullback.
No characteristic or residue-cardinality restriction is imposed.

`isReductive_baseChangeUnramified` proves that the actual model
`M.baseChangeUnramified` is reductive over `fixedFieldIntegers F`. It first
uses the published original-model reductivity theorem, which includes the
necessary smoothness argument, and then uses arbitrary reductive base change.
Its generic identification is the existing one of the original model's
actual coefficient extension.

`unramifiedModelGroupIso` takes a proof of
`StrictHenselianGenericIsoStatement`, a second actual reductive model `N`
over `fixedFieldIntegers F` with generic group equal to the actual scalar
extension of `G`, and the original hypotheses above. It supplies the
classification theorem's ring hypotheses using the published Henselian
property of this exact integer ring and the algebraic closedness of its
actual residue field. Algebraic closedness implies separable closedness.
Both models' supplied generic identifications give the required
isomorphism of their fraction-field fibres. Classical choice selects the
resulting abstract integral isomorphism from `N` to the original unramified
model.

`unramifiedModelGenericIso` computes the generic automorphism induced by
that chosen integral isomorphism using both original generic
identifications. `unramifiedModelIso` constructs a model isomorphism
compatible with exactly this automorphism.

Given an actual maximal-unramified integer-building datum `B`, a point
`x`, and an exact source identity
`N.integralPoints = B.oneStabilizer x`,
`integralPoints_eq_oneStabilizer_classifiedUnramified` identifies the
original unramified model's integral image with the one-group stabilizer
of the transported point. It uses the existing ambient transport of the
full valuation datum and its actual quotient equivalence. Thus the
subgroup on the left remains the original coefficient-extended model
image, with its original generic identification.

The provenance is internal: this module composes published arithmetic,
original-model reductivity, coefficient base change, the supplied
classification proposition and compatible model-image transport. It adds
no claim from the literature.

The strict-Henselian classification proof, the reductive source model,
the source building and its exact comparison remain explicit inputs.
This module constructs none of those inputs, no downstairs special point,
and no metric. It does not prove the unconditional
`BuildingComparisonStatement`.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
