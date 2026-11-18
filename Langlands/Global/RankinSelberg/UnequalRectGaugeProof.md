# The unequal-rank rectangular Whittaker gauge bound

`Langlands.Global.RankinSelbergGlobal.unequalRectGauge` proves the unchanged
published proposition `UnequalRectGaugeStatement.{u}`. It retains every number
field `F : Type u`, the compactness hypothesis on `AdeleQuotient F`, every
`t < r`, and every actual cuspidal operator realization `T` of rank `r + 1`.
For each such field, pair of ranks and realization, it gives one nonnegative
real threshold before quantifying over standard additive characters, vectors
and larger real exponents.

The integral is exactly the one in `RectWhittakerGaugeBound F h T`: the
extended norm of the dual Whittaker function, right translated by
`unfoldingWeyl F h`, is first integrated at `rectangularPoint F h p.out x`
against `rectangleMeasure F (r - (t + 1)) (t + 1)`. Its product with
`ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)` is then integrated against
`whittakerQuotientMeasure F (t + 1)`. The conclusion is that this iterated
lower integral is finite for every `σ` above the threshold.

The implemented proof applies the published reduction
`unequalRectGauge_of_simpleRootGauge` to the two published theorems
`whittakerSimpleRootMajorization` and
`adelicSimpleRootGaugeRectangularMellin`. These supply its exact two premises,
so the final theorem has no additional analytic hypothesis.

The reduction obtains common real exponents `β` and `τ ≥ 0` from
`translatedDualCuspWhittaker_majorization_of_simpleRoot`. This bridge applies
generic Whittaker majorization to the dual cusp-function space and the inverse
standard character. Right translation by the unfolding Weyl representative
preserves the majorant because that representative lies in the standard compact
subgroup and has determinant norm one. Consequently each character and vector
admits a gauge `Ξ` with

`‖translateFunction w' (dualFunction (cuspWhittaker ψ v)) g‖ₑ
  ≤ ENNReal.ofReal (detNorm(g) ^ β) * Ξ(g)`.

The exponents are chosen before the character and vector; the individual gauge
may depend on them. Rectangular Mellin convergence provides a nonnegative
threshold `C` before choosing any gauge with exponent `τ`. The reduction uses
`rectangularGaugeThreshold C β = max 0 (C - β)`. If `σ` exceeds this threshold,
then `σ + β > C`. The determinant identity for `rectangularPoint` absorbs the
external power `β`, and `rectangular_mellin_lt_top_of_majorant` transfers the
finite gauge integral at exponent `σ + β` to the required Whittaker integral at
exponent `σ`. This preserves the common threshold over all characters and
vectors.

All ranks allowed by `t < r` remain present, including the zero-row rectangle.
Both measures and the quotient representatives are those of the target
definition. This module is an internal composition of the three imported
Library results. Their paired Markdown explains the underlying majorization,
rectangular convergence and exponent transfer; this final assembly makes no
new attribution to an external literature statement.
