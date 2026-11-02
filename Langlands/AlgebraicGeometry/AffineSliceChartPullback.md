# Comparing affine slice pullbacks with their ambient scheme pullbacks

This internal construction considers morphisms `t,s : R → U`, an affine open
`V` in `U`, an affine open `W` in `R` mapping into `V`, and an ideal `I` of
`Γ(U,V)`. The affine quotient slice maps into `U` by its quotient spectrum
map followed by the chart open immersion.

`affineSliceChartToPullback` maps the pullback computed over `Spec Γ(U,V)`
into the full pullback over `U`. It uses the identity on the quotient slice
and the chart open immersions on `R` and `U`. Mathlib's pullback-map theorem
proves that this is an open immersion. Its second projection is the affine
second projection followed by the source chart map. When `W` also maps into
`V` under `s`, composition with `s` agrees with the affine `s` composite
followed by the target chart map, by naturality of the affine chart.
