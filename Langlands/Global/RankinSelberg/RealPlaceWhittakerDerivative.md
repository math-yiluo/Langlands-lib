# Real-place Whittaker regularity from smoothness and growth

This internal supporting result towards `RealPlaceFunctionalEquationStatement` is in namespace
`Langlands.Global.RankinSelbergGlobal`. It connects the proved actual global
Lie-curve differentiation theorem to the matrix-model right derivative in
the real local coefficient space.

`RealPlaceRestriction.oneParameter_realInclusion` proves that exponentiating
the real Lie direction supported at a chosen real place inserts precisely
the local real matrix exponential at that place. The proof applies
naturality of `NormedSpace.exp` to the continuous real and complex matrix
projection algebra homomorphisms. At the chosen place the projected
direction is `X`; at every other place it is zero, whose exponential is
identity. The resulting entrywise calculation proves equality in the full
mixed-coordinate matrix group. Transporting through the existing adelic
coordinate equivalence gives `adelicOneParameter_realInclusion`.

`lieOperator_realInclusion` identifies the full enveloping-algebra real Lie
generator of that supported direction with
`realPlaceLieAction w (1 ⊗ X)`. This is the Library's scalar-extension
inclusion formula, applied to the genuine actions.

For an actual cuspidal realization `T`, standard additive character `χ`,
real place `w`, finite adelic point `b` and actual vector `x`, let

```text
W(g) = cuspWhittaker F T χ x
  (realPlacePoint F (r+1) w g * finitePoint F (r+1) b).
```

`RealPlaceRestriction.rightDerivative_eq_restriction` proves that if `W` is
smooth, its matrix-model right derivative along a real matrix `X` is

```text
g ↦ cuspWhittaker F T χ
  (T.realization.realPlaceLieAction w (1 ⊗ X) x)
  (realPlacePoint F (r+1) w g * finitePoint F (r+1) b).
```

There are two computations of the derivative at zero of
`s ↦ W(g * matrixExpUnit (r+1) (s • X))`. The actual integral computation is
`WhittakerCurve.cuspWhittaker_hasDerivAt`, combined with the exponential
comparison, commutation with the finite adelic factor, and the action
comparison above. The smooth matrix-model computation is the Library's
`Archimedean.hasDerivAt_mul_matrixExpUnit_smul`. Uniqueness of the derivative
proves the equality. Differentiation under the Whittaker integral is
therefore proved, rather than retained as a separate premise.

`RealPlaceWhittakerSmoothGrowthStatement.{u}` retains only smoothness of all
such actual restrictions and a bound
`‖W g‖ ≤ C * realMatrixHeight g ^ N` for some real `C` and natural `N`.
`realPlaceWhittakerAnalytic_of_smoothGrowth` supplies the derivative clause
with the preceding theorem. The converse implication simply forgets that
clause.

`RealPlaceFunctionalEquationSmoothGrowthReductionStatement.{u}` states that
the local unequal-rank package, local positive equal-rank package, this
smoothness-and-growth statement, and the actual contragredient pair-factor
denominator comparison imply the exact Library statement
`RealPlaceFunctionalEquationStatement.{u}`.
`realPlaceFunctionalEquationSmoothGrowthReduction` is the composition with
the preceding actual-model reduction. It retains the free universe `u`.
None of the four inputs is proved here; the Library proves the
smoothness-and-growth statement as `realPlaceWhittakerSmoothGrowth` (module
`RealPlaceWhittakerAnalyticProof`). The unconditional full functional equation
is not proved by this module.
