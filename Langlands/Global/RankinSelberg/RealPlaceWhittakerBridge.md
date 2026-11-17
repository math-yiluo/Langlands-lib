# The real-place model bridge from coefficient regularity

This internal conditional reduction for Task 7400 is in namespace
`Langlands.Global.RankinSelbergGlobal`. It adapts Worker 5665's complex-place
bridge argument, using the real-place spanning proof in `RealPlaceIsotypic`
and the unconditional character and compact calculations in
`RealPlaceWhittakerEquivariance`.

The resulting `RealPlaceFunctionalEquationAnalyticReductionStatement.{u}`
states that the following four inputs imply the exact published
`RealPlaceFunctionalEquationStatement.{u}`:

1. `RealLocalUnequalJacquetStatement`, the local unequal-rank integral package;
2. `RealLocalPositiveEqualJacquetStatement`, the local equal-rank package for
   positive `r`;
3. `RealPlaceWhittakerAnalyticStatement.{u}`, coefficient regularity described
   below;
4. `RealPlaceContragredientPairLStatement.{u}`, equality of the dual denominator
   functions for actual contragredient parameters and inverse real blocks.

All four inputs remain open in this contribution. The already implemented
`RealLocalTheoryReduction` supplies the parameter signs, reflection and
unconditional `r = 0` equal-rank case. The local analytic inputs also retain
any continuous-globalization and measure-normalization comparison needed to
prove their integral assertions for the specified algebraic coefficient model.

For a number field with compact adele quotient, a standard adelic additive
character `χ`, an actual cuspidal realization `T` of `GL_(r+1)`, a real place
`w`, finite adelic point `b` and vector `x`, put
`W(g) = cuspWhittaker F T χ x (realPlacePoint F (r+1) w g * finitePoint F (r+1) b)`.
`RealPlaceWhittakerAnalyticStatement` asserts:

1. `W` is smooth for `Archimedean.matrixModel ℝ (r+1)`;
2. `‖W g‖ ≤ C * realMatrixHeight g ^ N` for some real `C` and natural `N`;
3. the restriction of the actual real-place Lie action of `1 ⊗ X` on `x`
   is the right derivative of `W` along each real matrix direction `X`.

The implemented proof has two steps. First,
`RealPlaceWhittakerIntertwinerStatement` asks that every compact/Lie-equivariant
standard-module map `A` give a Whittaker coefficient intertwiner, for both the
original character and its inverse. `restriction_mem_realWhittakerModel`
proves model membership for every vector in the supremum of the images of
these maps, by induction over that supremum. The range case is the defining
range inclusion in the local model; the zero and sum cases use the proved
linearity of the actual global Whittaker integral.
`realPlaceWhittakerModelReduction` applies `realPlaceIsotypic_eq_top` to the
irreducible global realization with its given parameter. This supplies model
membership for every actual global restriction.

Second, `exists_restriction_isRealWhittakerIntertwiner` constructs the linear
map `f ↦ W_(A f)` using `cuspWhittaker_add` and `cuspWhittaker_smul`. Its left
character and compact clauses are the preceding module's proved covariance
results. Its smoothness and growth clauses are the analytic premise for
`A f`. For Lie compatibility, the second clause of `IsRealPlaceMap` identifies
`A` of the source derivative with the actual Lie action on `A f`; the analytic
premise then identifies its coefficient with the derivative of `W_(A f)`.
The original and inverse characters have local parameters `a` and `-a`,
respectively.

Composing these steps with `realPlaceLocalTheoryReduction` proves
`realPlaceFunctionalEquationAnalyticReduction`. The proof retains a free
number-field universe `u`. It proves no part of the coefficient regularity
premise and does not prove the unconditional full functional equation.
