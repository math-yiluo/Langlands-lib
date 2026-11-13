# Unit criterion for the pointwise test algebra

This module proves `Langlands.Sheaf.Renard.PointwiseTestAlgebraUnitalIffCompactStatement`
as the exact theorem `pointwiseTestAlgebraUnitalIffCompact`, for every space universe.
It adds no hypothesis and leaves the published statement and its imports unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, II.2.4, Example, printed p.38 / PDF p.44, registered as
`renard-2026-representations-groupes-reductifs-padiques`.

For a two-sided unit `e`, choose a compact open neighborhood `U` of each point `x`.
Evaluating `e χ_U = χ_U` at `x` gives `e(x) = 1`. Thus the actual support of `e`
is all of `X`. The published compactness of test-function support proves that
`X` is compact. Conversely, for compact `X`, the characteristic function of `X`
is a test function and its pointwise products fix every test function.
This argument also covers the empty space.
