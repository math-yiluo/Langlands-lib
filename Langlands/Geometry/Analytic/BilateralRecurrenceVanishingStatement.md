# Vanishing of decaying bilateral multiplication recurrences

Authors: Worker 105 (formulation and intended route), Worker 214 (Lean statement
and documentation).

`Langlands.Analytic.BilateralRecurrenceVanishingStatement.{u,v}` is a
proposition with all its data quantified internally. For every
`K : Type u` with `NontriviallyNormedField K`, every `A : Type v` with
`NormedCommRing A`, `NormedAlgebra K A`, `CompleteSpace A` and
`IsNoetherianRing A`, every `f : A` and every `c : ℤ → A`, it asserts

```text
Filter.Tendsto c Filter.cofinite (nhds 0) →
(∀ n : ℤ, c (n - 1) = f * c n) →
∀ n : ℤ, c n = 0.
```

The universes `u` and `v` are independent. Cofinite convergence means that
for each positive real `ε` only finitely many integers `n` have
`ε ≤ ‖c n‖`; in particular, decay is required in both integer directions.
The norm, multiplication, scalar action and topology are the given ones
on the original normed algebra. Completeness is required only of `A`.
There is no ultrametric assumption on either `K` or `A`, no completeness
assumption on `K`, and no nonzero, reducedness, domain or invertibility
assumption on `A` or `f`. Closedness of ideals, a Laurent coefficient
normal form and exactness are not premises.

This is an internal, derived statement for the binary Laurent argument.
Its intended proof route uses the published theorem
`Langlands.Analytic.isClosed_ideal_of_noetherian_banach` from
`Langlands.Geometry.Analytic.ClosedIdealsBanach`, which proves that every
ideal of an algebra with exactly the displayed scalar, norm, completeness
and Noetherian hypotheses is closed. It also uses Mathlib's
`banach_steinhaus` from
`Mathlib.Analysis.Normed.Operator.BanachSteinhaus`: a pointwise bounded
family of continuous linear maps with complete domain has uniformly
bounded operator norms. Neither tool requires completeness of the scalar
field. These modules are imported without changing their declarations,
carriers or dependencies.

The proposed proof forms the ideal
`I = {a : A | f^m * a → 0 as m : ℕ tends to infinity}`.
Closedness makes its inherited normed space complete. The powers of
multiplication, restricted as continuous `K`-linear maps from `I` to `A`,
are pointwise bounded, so Banach–Steinhaus should supply a uniform
operator norm bound `C`. For fixed `k : ℤ` and `n : ℕ`, iterating the
recurrence expresses `f^m * c (k+n)` as `c (k+n-m)`; decay in the
negative direction places `c (k+n)` in `I`. The same iteration gives
`f^n * c (k+n) = c k`. The intended estimate
`‖c k‖ ≤ C * ‖c (k+n)‖`, together with decay in the positive direction,
would then force `c k = 0`. This is a proposed derivation and remains a
proof obligation; this module supplies only the exact proposition.

The intended application is to injectivity of multiplication by `X-f`
on the auxiliary annulus in the binary Laurent argument, after a separate
genuine Laurent coefficient normal form identifies its kernel equations
with this recurrence. This route permits nilpotents in the coefficient
algebra. The application, the coefficient normal form and all annulus
theorems remain separate obligations. No external source is being
credited with this standalone internal lemma, and no substantive proof
is supplied here.
