# The uniform weighted Whittaker–Schwartz estimate

`whittakerSchwartzGauge` proves exactly the existing proposition
`WhittakerSchwartzGaugeStatement.{u}`. It retains every number field in
universe `u` with compact additive adelic quotient, every natural rank
including zero, the full analytic decay class, and the common central
power bound. Its conclusion uses the actual adelic unipotent quotient
and the existing `whittakerQuotientMeasure`.

The proof combines the pointwise theorem
`whittakerSimpleRootMajorization` with the concrete full-rank torus
estimate `lintegral_gaugeSchwartzTorusMajorant_lt_top_of_large`, using
`whittakerSchwartzGauge_of_majorization_torusMajorants`. The pointwise
theorem supplies a nonnegative simple-root gauge exponent τ uniform in
the standard character and vector. For each such character and vector,
it bounds the Whittaker norm by `|det g|^β Ξ(g)`, where β is the one
exponent supplied by the central power hypothesis and Ξ is a genuine
simple-root gauge. No gauge or convergence assumption is added to the
target.

For this τ and rank r, choose

```text
D = τ + 3 + sum_(j=0,...,r) (j+1)*(r-j).
```

All terms are nonnegative. The torus theorem proves finiteness above D
for every pair of Schwartz–Bruhat factors, using any Haar measure on the
full `(r+1)`-fold idele torus. Here the proof chooses `Measure.haar`.
Local compactness and second countability of the idele group are
transported through `AdelicSchwartzMellin.ideleContinuousEquiv`; the
local measurable structure is its Borel structure.

The torus integrand contains the inverse of the actual diagonal
unipotent Haar modulus, the original simple-root weight, a Schwartz
factor on the adjacent ratios, a separate Schwartz factor on the last
diagonal idele, and the determinant power. In adjacent-ratio and last
coordinate variables, its scalar exponents are

```text
(j+1)*σ - τ - (j+1)*(r-j)  for j < r,
(r+1)*σ                    for j = r.
```

Above D every exponent exceeds three, as required by the rank-one
Mellin estimate. The torus theorem retains rank zero by treating the
empty first row as a singleton and retaining its finite scalar norm.

The reduction applies the compact-uniform kernel majorant and
`lintegral_gaugeSchwartzKernel_lt_top_of_torusMajorant` to convert this
torus convergence into finiteness on the actual Whittaker quotient.
Its final threshold is `max 0 (D - β)`. This is chosen before the
character, vector, last-row Schwartz function and integration exponent.
For σ above that threshold, σ + β exceeds D. Pointwise majorization and
the positive-real identity
`|det g|^β |det g|^σ = |det g|^(σ+β)` bound the requested lower integral
by the finite gauge integral.

This is an internal derived proof under the target's explicit analytic
hypotheses. Its provenance is the imported pointwise majorization,
Schwartz–Bruhat Mellin convergence, actual Haar-modulus calculation,
compact kernel majorization and quotient integration criterion. The
gauge argument motivating the published statement comes from
Jacquet–Shalika's global Rankin–Selberg analysis; this implementation
does not identify the generalized analytic-decay-class statement with
a verbatim theorem of that source.
