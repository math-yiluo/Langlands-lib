# The strong comparison of the two affine ground field extensions

The theorem
`Langlands.Analytic.AffineAnalytification.affineAnalytificationGroundFieldComparison`
proves the proposition
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationGroundFieldComparisonStatement.{u, u', v}`
of `AffineAnalytificationGroundFieldComparisonStatement`. The three universes
are independent and the hypotheses are exactly those of the statement. The
proof uses the standard axioms only.

The proof is `GroundFieldComparison.reduceStrongComparison`, from
`AffineGroundFieldComparison.Strong`, applied to
`affineAnalytificationChartBaseChange` of
`AffineAnalytificationChartBaseChangeProof`, which proves the fixed-radius
statement `AffineAnalytificationChartBaseChangeStatement`: at every positive
polyradius, the ground field extension of the chart of `P` is boundedly
isomorphic to the chart of `baseChangePresentation K L P`, compatibly with
the maps from `A` and `L ⊗[K] A`.

The reduction builds an explicit witness in three steps.

1. `AffineGroundFieldComparison.Charts`: for an original chart index `i` and a
   raw `L`-chart index `n` of at least the same radius, the mixed-radius
   pullback `rawPull i n` is the radius restriction of the base-change
   presentation from radius `n` to the radius of `i`, followed by the inverse
   fixed-radius isomorphism. It sends `1 ⊗ a` to `iota` of the original image
   of `a` and represents the radius-bounded affinoid domain.
2. `AffineGroundFieldComparison.Points`: the induced chart point maps do not
   depend on `n`, are compatible with the source restrictions and glue to a
   continuous map `pointFun` of the point spaces. Composed with
   `baseChangeMap` it is the scalar-extension projection, which is checked on
   point seminorms of elements of `A`. Each chart point map is an embedding
   whose image is the `baseChangeMap`-preimage of the original chart, and these
   preimages form a quasinet, so `pointFun` is a homeomorphism.
3. `AffineGroundFieldComparison.Strong`: at each admissible pair `(i, j)` the
   bounded pullback is the unique factorization of a mixed-radius pullback from
   a larger raw chart through the restriction to the target chart `j`. It
   satisfies the chart equation, the equation on `1 ⊗ a`, and represents the
   image locus. Restriction squares are checked after precomposition with a
   still larger raw restriction, so no radius inequality between a source chart
   and a containing target chart is used. Compatibility of the pullbacks follows
   from the directed target atlas.

The witness is therefore a compatible strong quasi-isomorphism, lies over the
original analytification through `baseChangeMap`, and sends the target chart
image of `1 ⊗ a` to `iota` of the source chart image of `a`, as the statement
requires.

Naturality in algebra maps, the comparison after saturation and localization,
and nonaffine schemes and spaces are not asserted here.
