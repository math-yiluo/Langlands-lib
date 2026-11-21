# The chart of `G(F ⊗ ℝ)` in regular coordinates, and injectivity of realization differentials

Module `Langlands.Global.InfiniteAdelicChartFormula` (namespace
`Langlands.Global.InfiniteAdelicGroupPoints`). Internal supporting result for the adapted Casimir
proof: it shows that the matrix differentials of place-wise closed realizations of a smooth affine
group scheme `G` over a number field `F` are jointly injective on the tangent space of the
infinite adelic point group at `1`, for the published atlas `smoothChartedSpace F G hsmooth`.

## Declarations

- `placeRegularChart F G hsmooth v x`: the regular chart, at the image of `x : G(F_v)`, of the
  chosen regular atlas `smoothAffineRegularAtlas` of the base change `G_v`. Its coordinates are
  quotients `numerator / denominator` of global regular functions of `G_v`, with denominators
  nonzero on its source (structure `RegularChart`).
- `extChartAt_apply`: the extended chart of `G(F ⊗ ℝ)` at `x` sends `g` to
  `v ↦ (placeRegularChart … v (atPlace F G v x)).homeomorph (affineBaseChangePointHomeomorph … (atPlace F G v g))`.
  This holds by definition (`rfl`): the published atlas is the pullback through the completion
  decomposition of the product of the place-wise atlases, each the pullback through base change of
  the chosen regular atlas.
- `mem_extChartAt_source_iff`: `g` is in the chart source exactly when, for every place `v`, the
  image of `atPlace F G v g` is in the source of the place-wise regular chart.
- `regularEvaluation_affineBaseChangePointHomeomorph`: evaluation of a global regular function of
  `G_v` at the base-changed point equals `affinePointEvaluation` at
  `affinePointsBaseChangeMulEquiv F F_v F_v G y` (`affinePointsRingPointHomeomorph_evaluation`).
- `eq_zero_of_zeroDeriv_realization` (main result). Let `ρ v` be a closed matrix representation
  of `G_v` for each infinite place `v`. If `X` is a tangent vector at `1` along which every entry
  `g ↦ (realizationMatrix F G v (ρ v) (atPlace F G v g)).val i j` has zero derivative (in the sense
  of `ZeroDirectionalDerivative.ZeroDeriv`), then `X = 0`.

## Proof of `eq_zero_of_zeroDeriv_realization`

1. The inverse-matrix entries also have zero derivative along `X`: they are smooth (composition of
   inversion, which is smooth on the published Lie group, with the smooth entries given by
   `contMDiff_iff_realizationMatrix`), the matrix times its inverse is `1`, and the matrix at `1`
   is `1` (`zeroDeriv_of_mul_eq_one`).
2. For each global regular function `b` of `G_v`, the function
   `g ↦ regularEvaluation (affineBaseChangePointHomeomorph … (atPlace F G v g)) b` has zero
   derivative along `X`: by `MatrixRepresentation.exists_polynomial_affinePointEvaluation` it is a
   polynomial in the entries and inverse entries (`zeroDeriv_aeval`).
3. Each coordinate `g ↦ extChartAt … 1 g v k` agrees near `1` (on the chart source) with
   `numerator_k / denominator_k` evaluated at the base-changed point (`RegularChart.apply_eq`), the
   denominator is nonzero at `1`, and the coordinate is smooth at `1` (`contMDiffAt_extChartAt`).
   So it has zero derivative along `X` (`ZeroDeriv.div`, `ZeroDeriv.congr`).
4. The derivative of the extended chart at its base point is the identity
   (`mfderiv_extChartAt_self`). Composing with the projection to the `(v, k)` coordinate and
   comparing derivatives gives `X v k = 0` for all `v` and `k`, so `X = 0`.
