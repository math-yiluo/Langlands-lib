# Countable-cell tests for finite positive Lp exponents

`Langlands.CountableCellLpStatement` bundles two elementary measure-theoretic
tests for a real-valued function on any measurable space. The ambient space
and countable index type have independent universes. The measure is arbitrary.
In both clauses the exponent `p : ℝ≥0∞` is nonzero and finite, so `p.toReal > 0`.
The bounds `b i` lie in `ℝ≥0∞`; infinite values are allowed and the products use
the usual extended-nonnegative-real conventions.

`CountableCellLpUpperStatement` assumes that `f` is almost everywhere strongly
measurable, that the sets `s i` cover the whole space, and that
`‖f x‖ₑ ≤ b i` on each `s i`. It asserts `MemLp f p μ` when

```
∑' i, (b i) ^ p.toReal * μ (s i) < ∞.
```

The covering sets need not be measurable or disjoint. Here `μ (s i)` is the
measure's value on an arbitrary set, and the upper integral comparison
remains valid using restriction and a measurable constant majorant.

`CountableCellLpLowerStatement` starts with `MemLp f p μ`. It assumes that the
sets `s i` are measurable and pairwise disjoint, and that
`b i ≤ ‖f x‖ₑ` on each `s i`. It concludes the same finite-sum inequality.
These cells need not cover the ambient space. No positivity or finiteness of
individual cell measures is separately required.

## Internal provenance

These statements package elementary consequences of the imported Mathlib
Lebesgue integral and Lp APIs; they are not translations of an external
representation-theoretic theorem. For the upper clause, use the countable-union
integral inequality, monotonicity of nonnegative real powers, and the integral
of a constant on each cell. For the lower clause, use the integral identity
for a disjoint measurable union, followed by monotonicity under restriction.
For a nonzero finite exponent, finiteness of the integral of `‖f x‖ₑ ^ p.toReal`
is equivalent to the finite Lp seminorm when the function is almost everywhere
strongly measurable.

## Intended use and limits

The upper clause can be applied to descended matrix-coefficient norms after
proving a countable Cartan covering, coefficient bounds and summability of the
resulting measure-weighted powers. The lower clause can detect an obstruction
to integrability from disjoint cells on which a coefficient has a lower bound.
This interface supplies none of those geometric, coefficient or summability
facts. It asserts no temperedness or Jacquet-exponent criterion.
