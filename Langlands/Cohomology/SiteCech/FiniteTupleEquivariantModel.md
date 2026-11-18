# Finite equivariant models from lifted tuple cones

This internal construction combines the supplied geometric tuple cones of
`FiniteCechDifferentials` with the signed finite boundaries of
`TwistedFreeRepresentableCochain`. It assumes full lifted actions on the chosen
finite representatives and equivariance of the face arrows.

`GlobalLift.withObject` uses an equality to give a supplied lift the specified
underlying object definitionally. Equality elimination proves that the result
is the original lift. `tupleLiftFamily` applies this normalization in one tuple
degree, and `tupleLiftFamily_eq` identifies the complete family with the input.
No action or eventual equivariance is created by normalization.

`tupleSignedBoundary` uses the canonical enumerated tuple reindexing for each
face, the transported universal tuple arrows, and coefficients `(-1)^j`.
Equivariance of every such face arrow is an explicit input. Its ordinary map
is definitionally `tupleFreeBoundary`, as proved by
`tupleSignedBoundary_ordinaryMap`.

The provenance is internal: only equality elimination and finite signed sums
are used, together with imported tuple-arrow definitions. This module does
not assert geometric existence, compatibility of arbitrary analytic lifts,
fixed coefficient sections, exactness, or the analytic comparison theorem.

`finiteFreeThreeTermModelOfCones` takes the ordinary limiting cones and basis
isomorphisms in every tuple degree, as required by the canonical Čech
presentation. It requires lifted objects only in degrees `n+2`, `n+1`, and `n`,
with equality of each underlying object to its specified basis representative.
It further takes eventual-equivariance proofs for these three finite families
and full-action equivariance of the upper and lower face arrows. It does not
require lifted actions or simultaneous action compatibility in other degrees.

The output is `FiniteFreeThreeTermModel J R S Q n`, where `Q` is the actual
`freeCechChainComplex` of the cover's representable coproduct arrow. The three
ordinary term isomorphisms are the inverses of the canonical `freeTermIso`
isomorphisms. Both ordinary differential squares are proved: normalization
makes each signed boundary's ordinary map definitionally the tuple boundary,
and the symmetry of `cechPresentationOfCones_free_inv_d` gives the required
square, at `n+1` and `n` respectively. Thus these squares are not additional
hypotheses of this constructor.

`finiteFreeThreeTermModelOfCones_middle` identifies the model's middle family
with the supplied middle lifts, using `tupleLiftFamily_eq`. In particular,
normalization preserves the action used for fixed coefficient sections. The
constructor itself needs ordinary module sheafification and local smallness;
it neither constructs twisted module sheafification nor requires finite
refinements. Under the further assumptions of the imported model API, the
output can be passed to `FiniteFreeThreeTermModel.equivariantModel` or
`.cochainLift`. For the latter, ordinary exactness and the fixed middle
sections representing the specified cochain remain inputs.

No existence of the geometric cones, the three lifted families, their eventual
equivariance, or equivariance of their faces is proved here. These analytic
inputs and the full global cohomology comparison remain open in this unit.
