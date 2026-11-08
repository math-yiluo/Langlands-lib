# Linearity of the Heisenberg cocycle under the point-to-Lie comparisons

Let `a` be a multipliable relative root of a smooth affine group `G` over a field `k`, let
`V = U_a / U_{2a}` be the quotient of the published `DoubleRootCommutatorPairing C`, and let `β`
be the cocycle of a Heisenberg normal form `M`. The module `RootQuotientLieEquiv` identifies
`V(k)` with the weight space `g_a` (`rootQuotientPointLieEquiv`). The published
`representedRootPointLieEquiv` identifies `U_{2a}(k)` with `g_{2a}`. This module shows that,
through these identifications, `β` on rational points is `k`-linear in each argument. The
intended use is the `k`-homogeneity fields of field data for quadratic unitary coordinates
(module `Geometry/Building/RootUnitaryHeisenbergSeparation`).

Provenance: internal. The proof reads both identifications in weight vector coordinates. There
the cocycle is linear over every coefficient algebra (published `coordinatePairing_smul`,
applied with the equivariance `cocycle_act` and the normalizations `cocycle_one_left` and
`cocycle_one_right` of the published `HeisenbergNormalForm`).

All declarations live in namespace `Langlands.GroupScheme.RelativeRoot`.

## Setting

`G` is smooth and affine over `Spec k`, the root groups `U` and `U₂` are affine, and so is
`C.V`. Further `hS : IsSplitTorus S`, `ha : a ≠ 0` and
`hhigh : ∀ n ≥ 3, n • a ∉ relativeRoots i`.

## The doubled root group

- `two_nsmul_ne_zero_of_isSplitTorus hS ha : 2 • a ≠ 0`.
- `doubleRootPointLieEquiv hS ha hhigh hj₂ : Additive (rationalPoints U₂) ≃+ weightSpace i (2 • a)`.
  It is the published `representedRootPointLieEquiv` for `2 • a`, which has no higher multiples
  that are roots (`hasNoHigherRoots_two_nsmul`), precomposed with `hj₂.pointsEquiv`.
- `doubleRootPointLieEquiv_apply`: its value is the differential of `j₂` applied to the
  point-to-Lie comparison `vectorPointLieEquiv` of the weight vector coordinates
  `weightVectorCoordinatesOfNoHigherRoots hS i _ _ hj₂` (published).

## Results (namespace `DoubleRootCommutatorPairing`)

- `vectorPointLieEquiv_smul_of_rootQuotientPointLieEquiv`: if the images of `v'` and `v` in
  `g_a` under `rootQuotientPointLieEquiv` satisfy `λ(v') = c λ(v)`, the same holds for their
  images under the point-to-Lie comparison of the weight coordinates chosen in
  `rootQuotientPointLieEquiv`. The inclusion `g_a ⊆ Lie(G)` composed with the inverse of
  `rootQuotientLieEquiv` is an injective linear map.
- `rationalCoeffEquiv_lift_comp`: passing to coefficient points commutes with evaluating the
  cocycle on a pair of rational points.
- `vectorPointLieEquiv_cocycle_smul_left` and `vectorPointLieEquiv_cocycle_smul_right`. These
  are stated for points `x, x', y` with coefficients in `k` and a scalar `r`. If
  `vectorPointLieEquiv (x') = r · vectorPointLieEquiv (x)` in the coordinates of `V`, then the
  same relation holds between the values of the cocycle at `(x', y)` and `(x, y)`, in the
  coordinates of `U₂`. The right version is the same for the second argument. Proof: the
  point-to-Lie comparison is the inverse of the linear coordinate map `vectorLieCoordinates`
  applied to the point coordinates. In point coordinates the cocycle is the published
  `coordinatePairing`, which is linear in each argument by `coordinatePairing_smul`.
- `doubleRootPointLieEquiv_cocycle_smul_left M c v v' w`: for rational points `v, v', w` of
  `C.V` with `λ(v') = c λ(v)` in `Lie(G)`, the image of `β(v', w)` under
  `doubleRootPointLieEquiv` is `c` times that of `β(v, w)`.
- `doubleRootPointLieEquiv_cocycle_smul_right M c v w w'`: the same for the second argument.

## Scope

The module proves `k`-linearity only. It does not identify the weight spaces with fields and
does not construct any coordinates.
