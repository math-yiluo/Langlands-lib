# Finite rational pullback under the relative Laurent Gauss section

This internal construction proves that the inverse image of every actual
rational-chart locus under the relative Laurent Gauss section is a finite union
of actual rational-chart loci over the original affinoid algebra. It extends the
finite polynomial coefficient calculation in
`GaussLaurentRationalDecomposition` to arbitrary elements of the actual closed
Laurent quotient.

## Parameters and imported constructions

Let `K : Type u` be a complete ultrametric normed field, let `A` be an actual
presented affinoid algebra over `K`, and let `t > 0` be any real radius.
`RelativeLaurentAnnulus.algebra K A t` is the actual enlarged scalar weighted
Tate quotient, retaining the old relations and imposing that its two new
coordinates are inverse. The imported continuous map `gaussSection K A t`
sends each base spectrum point to its completed-residue Laurent Gauss point.
Its underlying function is `sectionPoint K A t`.

The finite Laurent expression map `polynomialMap K A t` has dense range in this
actual quotient norm. For positive radii `r_i` and threshold `q > 0`, the
polynomial coefficient construction already expresses the inequalities

```text
q ≤ s_x(g)  and  s_x(f_i) ≤ r_i s_x(g) for every i
```

as a finite union of actual ambient rational charts when `f_i` and `g` are
images of finite Laurent expressions. Here `s_x` denotes the actual
`sectionPoint K A t x` seminorm. The numerator index type is finite and may lie
at an independent universe `v`.

## Uniform approximation and exact preservation

`exists_polynomial_ratio_approximation` chooses a finite Laurent approximation
`g'` with `‖g - g'‖ < q`, and approximations `f'_i` with
`‖f_i - f'_i‖ < r_i q`. Density supplies these choices in the actual quotient
norm. The choices are independent of the spectrum point.

The two private perturbation lemmas use the published nonarchimedean property
of actual spectrum seminorms and their domination by the norm:

* If `‖a - b‖ < x(b)`, then `x(a) = x(b)`. Apply the strict-dominance strong
  triangle identity to `(a - b) + b`.
* If `‖a - b‖ < c`, then `x(a) ≤ c` if and only if `x(b) ≤ c`. In each direction,
  apply the strong triangle inequality to the difference and the other element.

Whenever `q ≤ s_x(g)`, the first lemma identifies `s_x(g')` with `s_x(g)`.
The same argument in the reverse direction works whenever `q ≤ s_x(g')`.
For each numerator, its approximation error is less than `r_i q` and therefore
less than the corresponding bound `r_i s_x(g)` or `r_i s_x(g')`. The second
lemma preserves its non-strict upper inequality, including equality at the
boundary. These facts prove the exact equivalence of the original and
approximating positive-threshold rational inequalities at every base point.

`exists_finite_ratio_charts` composes this equivalence with
`exists_finite_polynomial_ratio_charts`. It supplies a natural number `m` and
actual `D : Fin m → RationalChart K A` whose union is exactly the original
positive-threshold locus for arbitrary actual Laurent quotient data.

## Actual rational-chart pullback

For `d : RationalChart K (algebra K A t)`, the existing theorem
`RationalChart.exists_pos_le_denominator` supplies `q > 0` such that
`q ≤ y(d.denominatorClass)` for every point `y` of `d.locus`.
Its proof uses compactness of the actual rational locus, continuity of
denominator evaluation, and unit generation to exclude a zero denominator.
It also covers an empty locus.

`exists_finite_rational_pullback` applies the preceding finite decomposition to
the actual quotient classes of `d`'s displayed numerator and denominator series,
with `d.radii`. Membership in `d.locus` is precisely its list of rational
inequalities; adding the chosen denominator lower bound does not change that
set. Consequently

```text
sectionPoint K A t x ∈ d.locus
  iff
x ∈ (D j).locus for some j : Fin m.
```

`rationalPullbackCharts K t d` chooses the resulting pair of a natural number
and a finite family of actual ambient charts. The theorem
`mem_rationalPullbackCharts` gives its pointwise property, and
`preimage_gaussSection_rational_locus` states the same property as equality of
the section inverse image with the finite union of these loci.

## Provenance and scope

This is a derived internal argument using the published density, spectrum
nonarchimedean estimates, compact denominator bound, and finite coefficient
decomposition. No external numbered theorem is asserted as its direct source.
All approximation and rational-chart data refer to the actual scalar quotient
carriers and their constructed norms.

The result retains the full universe `u`, arbitrary positive real radii, trivial
valuations, arbitrary closed presentation ideals, empty original coordinate
tuples, nonreduced and zero quotient algebras, and empty rational loci. No
independence of `t`, strictness, or nonzero hypothesis is assumed. The result
constructs charts and identifies their union as a subset of the base spectrum;
it does not construct a scalar-field recasting, prove radical-radius
strictification, or prove `Domain.FiniteRationalCoverStatement` for all full
represented domains.
