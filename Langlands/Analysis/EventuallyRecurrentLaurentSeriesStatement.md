# Uniform Laurent rationality for eventually recurrent sequences

Worker 356 authored this pair from Worker 656's interface specification.

## Declaration and scope

`Langlands.Analysis.EventuallyRecurrentLaurentSeriesStatement` is the sole new
public declaration in
`Langlands.Analysis.EventuallyRecurrentLaurentSeriesStatement`. It is a closed
`Prop` definition, with no parameters or universe parameters. This module states
an analytic and algebraic prerequisite for the valuation-shell approach to
one-variable Mellin integrals. It supplies no proof.

The objects are Mathlib's `LinearRecurrence ℂ`, `Polynomial ℂ`,
`LaurentPolynomial ℂ` and `RatFunc ℂ`. Denominator clearing uses the existing
ring homomorphism `Langlands.RankinSelberg.laurentToRatFunc`, which sends the
Laurent monomial `T n` to `RatFunc.X ^ n` for every integer `n`. In particular,
the clearing equation is an identity in the actual rational function field.

## Exact clauses and uniformity

For every complex linear recurrence `E`, introduce locally the polynomial

```text
Q = 1 - ∑ i : Fin E.order, C (E.coeffs i) * X ^ (E.order - i.val).
```

The proposition first asserts `Q.coeff 0 = 1`. For every index in the sum,
`i.val < E.order`, so the exponent `E.order - i.val` is positive; this is
natural subtraction with no truncation in these summands.

Next it asserts that there exists a real radius `ρ > 0`. This choice occurs
before the positive weight, coefficient sequence and cutoffs. Thus one `ρ`
depends only on `E` and works for all the following data simultaneously.

For every `m : ℕ` satisfying `0 < m`, introduce locally

```text
D : LaurentPolynomial ℂ = (Q.comp (Polynomial.X ^ m)).toLaurent.
```

Here `Polynomial.comp` substitutes `X ^ m` into `Q`, and `toLaurent` is the
ordinary polynomial inclusion into the Laurent polynomial ring. The statement
asserts `D ≠ 0` before quantifying over sequences. This denominator depends
only on `E` and `m`, and has no dependence on the radius witness or sequence.

Now let `c : ℤ → ℂ`, `L : ℤ` and `N : ℕ` satisfy:

1. `L ≤ (N : ℤ)`;
2. `c n = 0` for every integer `n < L`;
3. `E.IsSolution (fun j : ℕ => c ((j : ℤ) + (N : ℤ)))`.

The third condition says that the natural sequence `a j = c (j + N)`
satisfies exactly Mathlib's recurrence convention:

```text
a (j + E.order) = ∑ i : Fin E.order, E.coeffs i * a (j + i.val)
```

for every `j : ℕ`. No recurrence condition is imposed on the finite head
`L ≤ n < N`.

The conclusion chooses `R : RatFunc ℂ` and `P : LaurentPolynomial ℂ` such
that

```text
laurentToRatFunc P = laurentToRatFunc D * R.
```

Thus `D` clears the denominator of `R` with a Laurent polynomial numerator.
The numerator is allowed to have negative exponents. Both `R` and `P` may
depend on the sequence and cutoffs as well as `E` and `m`; neither may depend
on the evaluation point.

For every `z : ℂ` with `z ≠ 0` and `‖z ^ m‖ < ρ`, the same witnesses satisfy
all three conclusions:

1. `Summable (fun n : ℤ => c n * (z ^ m) ^ n)`;
2. `R.denom.eval z ≠ 0`;
3. `∑' n : ℤ, c n * (z ^ m) ^ n = RatFunc.eval (RingHom.id ℂ) z R`.

The exponent `m` is a natural power; the outer exponent `n` is an integer
power (`zpow`). The nonzero condition on `z`, together with `m > 0`, ensures
that negative powers have their usual meaning. `Summable` is actual
unconditional summability in `ℂ`, and `∑'` is Mathlib's sum indexed by all
integers. It is not a formal Laurent series or a prescribed ordering of a
conditionally convergent bilateral sum.

`R.denom` is Mathlib's reduced polynomial denominator of the rational
function `R`. The second conclusion states nonvanishing of that denominator
at `z` itself, where `R` is evaluated, rather than at `z ^ m`. It guards the
third conclusion against the totalized behavior of `RatFunc.eval` at poles.
The clearing polynomial `D` is not asserted to be the reduced denominator.

In schematic form the order is

```text
∀ E, let Q := …;
  Q.coeff 0 = 1 ∧ ∃ ρ > 0, ∀ m > 0, let D := …;
    D ≠ 0 ∧ ∀ c L N, hypotheses → ∃ R P, clearing ∧ ∀ z, guards → conclusions.
```

All auxiliary objects are local bindings or quantified witnesses.

## Boundary cases

`L` may be negative, and the finitely many negative powers are included in
the Laurent head. `N` may be zero. There is no positivity condition on `L`
or on `E.order`, and no nonzero condition on `c`, `P` or `R`.

If `E.order = 0`, the defining sum for `Q` is empty and `Q = 1`. The
recurrence forces the tail `c (j + N)` to vanish, but the finite head may
remain nonzero; the resulting series is a Laurent polynomial. If `c = 0`,
the conclusions allow `R = 0` and `P = 0`. The evaluation point zero is
excluded even when a particular sequence has no negative terms.

Summability, exponential growth estimates, rationality, and denominator
clearing are conclusions or possible proof tools, not extra hypotheses.
There are no local fields, measures, integrals, complex spectral powers or
half-plane bounds in this proposition.

## Relation to the existing natural-series theorem

The published theorem
`Langlands.Analysis.linearRecurrenceGeneratingSeriesStatement_proof` in
`Langlands.Analysis.LinearRecurrenceGeneratingSeriesProof` proves
`Langlands.Analysis.LinearRecurrenceGeneratingSeriesStatement`. Its
supporting lemmas live in the namespace
`Langlands.Analysis.LinearRecurrenceGeneratingSeries` in that proof module.
It supplies the same `Q`, a positive radius depending only on `E`, and, for
each natural solution `a`, a polynomial `A` with

```text
Summable (fun j : ℕ => a j * w ^ j),
Q.eval w ≠ 0,
∑' j : ℕ, a j * w ^ j = A.eval w / Q.eval w
```

whenever `‖w‖ < ρ`. This new statement imports its statement module without
redefining or reproving that ordinary generating-series result.

For guidance toward a future proof, split the integer sequence into the
finite head `L ≤ n < N` and the tail `n = N + j`, and apply the existing
theorem to `a j = c (j + N)` at `w = z ^ m`. The head is represented by the
Laurent polynomial `H = ∑_{L ≤ n < N} c n * T (m * n)`, with the integer
cast of `m` understood. The tail is represented by
`X ^ (m * N) * A(X ^ m) / Q(X ^ m)` in the rational function field.
Consequently multiplying the sum of head and tail by `D` leaves a Laurent
polynomial. This explains why changing the cutoffs or finite head does
not require a new denominator or radius.

To obtain the reduced-denominator guard, a future proof must also justify
regularity after this rational-function construction. Clearing the
negative exponents in `H` gives an ordinary polynomial quotient whose
denominator is a power of `X` times `Q(X ^ m)`. Both factors are nonzero
at an admissible `z`. The reduced denominator divides a denominator in
such a presentation, so it too is nonzero there. This is a proposed proof
route, not a proof implemented by this module.

## Derived provenance and original sources

This interface is an internal derived formulation motivated by the
one-variable Mellin argument. It is not a separately numbered theorem in
either source below and does not quote either source as asserting this
exact recurrence proposition.

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin-Selberg Convolutions*, American Journal of Mathematics **105**
  (1983), 367–464, proof on printed pp. 391–392, especially display (6)
  and the following convergence, rationality and common-denominator
  paragraphs on p. 392 (one-based PDF pp. 26–27). Registered source:
  `jpss-1983-rankin-selberg`; retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
  SHA-256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
  *Automorphic forms on GL(3) I*, Annals of Mathematics (2) **109**
  (1979), 169–212, §(2.2), definition of a finite function immediately
  before Proposition (2.2), printed p. 181 (one-based PDF p. 14).
  Registered source: `jps-1979-gl3-i`; retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`;
  SHA-256
  `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.

The cited pages were read directly and visually. On 2026-10-29 no
`notes/errata` directory was present in the project, supplied Library or
workspace; the registered source entries were checked as well.

JPS defines finite functions by continuity and a finite-dimensional span
of translates. JPSS reduces the local integral to finite sums of products
of one-variable integrals with positive integer weights in display (6),
then obtains convergence for large real part, rationality in `X = q^(-s)`
and a denominator independent of the varying Schwartz functions.

In the project's valuation-shell route, finite translation orbits yield
recurrences for the eventual coefficient tails, while compact support
provides a lower cutoff. The present proposition isolates the subsequent
analytic and algebraic step, including the substitution `X ↦ X ^ m`.
Deriving the shell coefficients, relating them to actual integrals,
passing from a punctured disc to a spectral half-plane, and assembling
the full `Langlands.RankinSelberg.OneVariableMellinStatement` remain
separate obligations.

## Imports and environment

The imports are the existing natural-series statement and
`Langlands.Representation.RankinSelberg.RationalZeta`, the latter providing
the actual Laurent embedding and Mathlib's rational-function APIs.
The target environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Existing Library pairs are
unchanged. Compilation and proposition inspection establish well-formedness
only; the exact mathematical proof is a later task.
