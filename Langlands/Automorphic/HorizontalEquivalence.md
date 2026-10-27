# Equivalence transport of actual horizontal cochains and differentials

For a number field `F : Type u`, natural rank `n` and full operator
realizations `S`, `T : OperatorRealization F n`, this internal construction
transports the existing horizontal full-compact-equivariant spaces and their
finite adelic representations by a full operator equivalence
`e : S.Equivalence T`. Scalars are complex and the number-field universe is
arbitrary. The equivalence of spaces allows every natural rank and cochain
degree, including zero. Differential naturality requires positive rank, with
no restriction on the natural cochain degree.

`Equivalence.horizontalEquiv e q` has source
`S.horizontalFiniteRepresentation q` and target
`T.horizontalFiniteRepresentation q`. Its complex-linear equivalence is the
existing `horizontalCoefficientEquiv F n q e.compactRestriction`, which
postcomposes values by `e` and uses its inverse for the reverse map. Thus
both directions preserve every-slot horizontality for the actual compact
image and equivariance for the full standard infinite compact group. Its
finite intertwining equation is precisely the one already proved for
`Intertwiner.horizontalMap e.toIntertwiningMap q`.

`horizontalEquiv_apply` identifies the value at a reduced Lie tuple `X`
with `e (f.val X)`. `horizontalEquiv_toLinearMap` identifies its underlying
linear map with the forward horizontal map of `e.toIntertwiningMap`.
Both formulas follow by reflexivity. `horizontalEquiv_differential`
states that this equivalence commutes with the actual horizontal
differential in successive degrees. It is the preceding horizontal-map
naturality theorem for the same full intertwiner, with no change to the
differential or coefficient action.

The provenance is internal coefficient postcomposition from
`ArchimedeanHorizontal.horizontalCoefficientEquiv`, the compact restriction
in `OperatorCompactCompatibility`, and finite-equivariant transport and
differential naturality in `HorizontalTransportCore`. No new external
source identification is asserted. This unit transports the given concrete
spaces; it does not construct square zero, cycles, boundaries, cohomology,
smoothness of the horizontal representations or general tensor coefficients.

Authorship: Worker 2.
