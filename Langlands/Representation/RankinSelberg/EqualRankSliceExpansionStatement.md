# Conditional equal-rank determinant-series expansion

Author: Worker 594.

The module
`Langlands.Representation.RankinSelberg.EqualRankSliceExpansionStatement`
defines the proposition
`Langlands.RankinSelberg.EqualRankSliceExpansionStatement.{uF}`.
It states the conditional determinant-partition argument for the actual
equal-rank JPSS integral. The proposition is not proved in this module.

## Original source and conditional generalization

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, Section 4.2, printed pages 406–407, formulas (4.2.1)–(4.2.2).
The registered original is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 406–407 are zero-based PDF pages 41–42 in this retained scan;
both pages were read visually. No source-specific registered errata note
was found in the project or current Library `notes/errata` locations.

For actual rank `r = n + 1` the source partitions by

`G_r^m = {g ∈ GL_r(F) : |det g| = q^(-m)}`, for `m ∈ ℤ`,

and defines the coefficient (4.2.1)

`Ψ^m(W, W'; Φ) = ∫_(N_r \ G_r^m) W(g) W'(g) Φ(η_r g) dg`.

Here `η_r = (0, …, 0, 1)`, so `η_r g` is the last row of `g`.
On printed page 407, the source uses convergence of (2.4.1) for large
`Re(s)` and Fubini to obtain convergence of the coefficients and (4.2.2):

`Ψ(s, W, W'; Φ) = Σ_(m ∈ ℤ) q^(-m*s) Ψ^m(W, W'; Φ)`.

The source's convergent half-plane comes from a separate analytic theorem.
This statement isolates the elementary partition implication at an
explicitly assumed convergent parameter. It generalizes that implication
to every measure on the fixed Borel structure, and to all functions in
the existing standard and inverse Whittaker-function spaces. Their
covariance makes the integrand descend to the actual quotient. The
conditional implication uses the measurable determinant partition and
global Bochner integrability, without representation-theoretic growth or
measure-invariance hypotheses.

## Complete telescope

The declaration has just the field universe parameter `uF`. Its parameters
are `{p : ℕ}`, `[Fact p.Prime]`, `F : PadicField.{uF} p`,
`T : F.TopologicalData`, and `n : ℕ`. The actual rank is `n + 1`, and
`n = 0` is included.

Inside the proposition, `letI := T.topology` supplies the field topology
and hence the induced quotient topology. The measurable structure is
exactly `borel (LeftUnipotentQuotient n F.Carrier)`, also installed with
`letI`. This is the same structure used by the imported slice coefficients.
The proposition then universally quantifies over:

- every measure `μ : Measure (LeftUnipotentQuotient n F.Carrier)` for that
  fixed Borel structure;
- every `ψ : UnitaryAdditiveCharacter F.Carrier`, which already includes
  continuity, unitarity and nontriviality;
- every `W : WhittakerFunctions ψ n` and
  `W' : InverseWhittakerFunctions ψ n`;
- every `Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)`;
- every `s : ℂ`.

For each such tuple there is exactly one premise:

`EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s`.

By the imported definition, this means global Bochner integrability of
`equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ s` with respect
to `μ`.

Write `a(m) = equalRankSliceCoefficient T μ ψ W W' Φ m`,
`q = T.residueCardinality`, and `z = spectralPoint q s = (q : ℂ)^(-s)`.
The consequent is the conjunction of all three assertions:

1. `SliceIntegrable T μ
   (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0)`.
   This is genuine integrability on every determinant slice of the
   zero-parameter integrand used to define `a(m)`. It does not require
   global convergence at zero.
2. `Summable (fun m : ℤ => ‖a(m) * z ^ m‖)`, a summability assertion for
   nonnegative real norms of the complex scalar terms.
3. `HasSum (fun m : ℤ => a(m) * z ^ m)
   (equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ s)`.
   This is convergence of the unordered sum indexed by all integers to
   the actual global quotient integral at `s`.

The exponent in `z ^ m` is the integer exponent. Since `q > 1`, the
spectral point is nonzero, and the slice weight is exactly `q^(-m*s)`.
There is no rank shift or truncation of the integer index. All three
conclusions occur inside the universal quantifier over convergent
parameters; slice integrability follows whenever any one such parameter
is given, and the expansion holds at every such parameter.

## Existing interfaces and remaining proof obligation

The module imports
`Langlands.Representation.RankinSelberg.DeterminantSlices` by Lean name,
reusing the existing actual quotient, integrand, integral and coefficients.
It introduces no replacement for any of those definitions.

A proof of the declared proposition remains required. The available route
is to use `sliceIntegrable_of_integrable` at the convergent parameter and
`sliceIntegrableAt_equalRankIntegrand_iff` to transfer integrability to
zero on every slice. The existing measurable, pairwise disjoint covering
of determinant slices permits
`MeasureTheory.hasSum_integral_iUnion`; the identity
`setIntegral_equalRankIntegrand_determinantSlice` identifies its summands
with `a(m) * z ^ m` without any additional integrability premise.
Applying the partition argument to the norm integrals and using the
norm-of-integral bound supplies absolute scalar summability. This is a
description of the remaining proof route, not a proof supplied here.

No representation, coefficient-model membership, smoothness, Whittaker
type, irreducibility, compatible quotient Haar measure, local finiteness,
or half-plane convergence is a premise. Slice integrability, summability
and the expansion are conclusions. The proposition makes no claim of
unconditional convergence, a lower support bound, rational continuation,
analytic factor existence, a functional equation or multiplicativity.
