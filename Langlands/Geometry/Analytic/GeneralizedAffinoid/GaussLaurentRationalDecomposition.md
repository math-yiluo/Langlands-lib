# Finite rational decomposition of weighted Laurent inequalities

This internal construction gives actual ambient rational charts for the
positive-threshold rational inequalities of finite Laurent expressions under the
relative Gauss section. It uses the published quotient, polynomial evaluation and
fixed-support norm formula in `RelativeLaurentGaussContinuity`. It is a derived
coefficient calculation, with no claim to be a separately numbered result from
the literature.

## Parameters and actual charts

Let `K : Type u` be an ultrametric normed field, let `A` be an actual presented
affinoid algebra over `K`, and let `t > 0`. Completeness of `K` is needed for the
Gauss-section statements, but not for constructing the charts or computing their
loci. A finite numerator index type may have an independent universe `v`.

`RationalChart.boundedRatios b q hq a r hr` constructs a chart with quotient
denominator `b`, numerator family `a`, positive radii `r`, and the extra numerator
`1` with radius `q⁻¹`. Actual scalar-series representatives of the quotient
elements are supplied by `coefficientRepresentative`. The unit numerator proves
unit generation without an ideal assumption on `b` and `a`. Its locus is exactly

```text
q ≤ x(b)  and  x(a_i) ≤ r_i x(b) for every i.
```

The arbitrary finite index type is enumerated using `Fintype.equivFin`, so the
result has the finite scalar presentation required by `RationalChart`.

## Weighted coefficients and the selected chart

For a finite Laurent expression `p : AddMonoidAlgebra A ℤ`, write

```text
M_x(p) = sectionPoint K A t x (polynomialMap K A t p).
```

The imported fixed-support formula expresses this as the maximum of
`x(p_n) t^n` over the original coefficient support, with value zero for empty
support. The original support is retained even when a coefficient vanishes at
`x`. The two lemmas `sectionPoint_polynomialMap_le_iff` and
`exists_weightedCoefficient_eq_sectionPoint` respectively characterize a
nonnegative upper bound by all weighted coefficient bounds and show that a
positive value is attained at an exponent in that fixed support.

Fix finite numerator expressions `f_i`, a denominator expression `g`, positive
radii `r_i`, and a threshold `q > 0`. For each integer `n`,
`polynomialRatioChart K t f g r hr q hq n` uses denominator `g_n`. It imposes:

* the lower bound `q / t^n ≤ x(g_n)`;
* for every exponent `k` in the fixed support of `g`, the ratio bound
  `x(g_k) ≤ (t^n / t^k) x(g_n)`;
* for every `i` and every `k` in the fixed support of `f_i`, the ratio bound
  `x(f_ik) ≤ (r_i t^n / t^k) x(g_n)`.

All these radii are positive because `t`, `q`, and the `r_i` are positive.
The chart is constructed by `boundedRatios` with a finite sum of the denominator
support and the dependent sum of the numerator supports. The extra unit
numerator again makes generation unconditional. The theorem
`mem_locus_polynomialRatioChart` multiplies by the positive weights to identify
its locus with the weighted coefficient inequalities.

## Finite decomposition and proof

`polynomial_ratios_iff_exists_chart` proves, for every base spectrum point `x`,

```text
q ≤ M_x(g)  and  M_x(f_i) ≤ r_i M_x(g) for every i
  iff
x belongs to polynomialRatioChart(..., n)
  for some n in the fixed support of g.
```

In the forward direction, positivity of `M_x(g)` supplies a support exponent
attaining its maximum. The denominator coefficients are bounded by this maximum,
and the numerator bounds give every corresponding coefficient inequality.
In the reverse direction, the chart bounds all denominator coefficients by the
selected term. The selected exponent lies in the denominator support, so that
term also lies below the maximum. These two bounds identify it with `M_x(g)`.
The numerator coefficient bounds then recover the original rational inequalities.

`exists_finite_polynomial_ratio_charts` enumerates the denominator support to
give a natural number `m` and actual charts `D : Fin m → RationalChart K A` with
the same pointwise equivalence. If the denominator support is empty, the
positive-threshold locus is empty and `m = 0` is allowed.

## Scope

The coefficient constructions retain arbitrary positive real radii, arbitrary
closed presentation ideals, empty coordinate tuples, trivial valuations,
nonreduced and zero quotient algebras. No independence of `t` is assumed.
This unit handles finite Laurent polynomial data with a supplied positive
denominator threshold. It does not approximate arbitrary quotient elements,
strictify affinoid presentations, or prove
`Domain.FiniteRationalCoverStatement`.
