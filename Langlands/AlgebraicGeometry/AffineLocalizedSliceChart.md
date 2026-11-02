# Localized affine slices in ambient scheme pullbacks

This internal construction combines affine quotient pullbacks with affine
charts. For morphisms `t,s : R → U`, choose affine opens `V` in `U` and `W`
in `R` with `W` mapping into `V` under both maps. Let `A = Γ(U,V)` and
`B = Γ(R,W)`. The map induced by `t` determines the equations of the slice;
the separate map induced by `s` determines the etaleness hypothesis.

`affineLocalizedSliceChartToPullback` maps the spectrum of the quotient of
`B[1/g]` by the extended ideal `I` into `Spec(A/I) ×_U R`. It is the
composition of the localized affine quotient open immersion and the affine
chart pullback open immersion, so is itself an open immersion. Its second
projection is the affine second projection followed by the chart map.

If the localized quotient is etale over `A` for the map induced by `s`,
the composite of this open immersion with the second projection and `s`
is etale. The proof uses the affine etaleness calculation, the chart
comparison formula, and the fact that a chart inclusion is etale.

If a prime `q` of `B` avoids `g` and contains the pullbacks of `I`, it lifts
to this localized quotient. Its image in the full scheme pullback projects
to the chart image of `q`. Cancelling the open immersion's stalk
isomorphism transfers formal etaleness to the stalk of the ambient second
projection followed by `s`. No finite presentation assumption on this
ambient morphism is needed for that conditional result.

Finally, a finitely generated ideal `I` makes `Spec(A/I) → U` locally of
finite presentation: the quotient is a finitely presented `A`-algebra and
the target chart inclusion is locally of finite presentation.

All results are derived from the imported affine and chart helpers and
Mathlib's finite presentation and etale composition APIs. Selecting
equations, establishing a good-point hypothesis, and constructing a
globally surjective slice remain separate obligations.
