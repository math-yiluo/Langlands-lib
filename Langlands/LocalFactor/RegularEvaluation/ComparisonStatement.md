# Compatibility of regular reciprocal evaluation with local-factor adapters

This module states one internal comparison family for the published
[common interface](Definitions.md) and [adapters](Adapters.md). Its exact target
is `Langlands.LocalFactor.RegularEvaluation.ComparisonStatement`; the four
named component definitions and the aggregate return `Prop`. This contribution
contains statements only. A later proof must prove this published aggregate.

## Common notation and exact scope

For a denominator `d : X → K`, write `Point d` for the support subtype
`{x : X // d x ≠ 0}` and `value d x` for `(Units.mk0 (d x.val) x.property)⁻¹`.
All value equalities below are equalities of units, in `Kˣ` or `ℂˣ`.
For each equivalence `e : S ≃ Point d`, the input clauses are exactly

- `∀ x : S, (e x).val = x.val`;
- `∀ y : Point d, (e.symm y).val = y.val`.

Thus each equivalence preserves the original input in both directions. The
already constructed equivalences supply their inverse laws; the statement adds
explicit carrier and evaluator comparisons.

For the three specialized APIs whose regular domain is a subtype rather than a
separate predicate, the exact domain clause uses
`(∃ x : S, x.val = z) ↔ d z ≠ 0`. This asserts that the image of the subtype
projection is precisely the nonzero domain, without choosing a regular point
at an excluded input. The p-adic API has a separate predicate, so its clause
compares that predicate directly with polynomial nonvanishing.

## Polynomial Euler comparison

`EulerComparison A` keeps arbitrary `K : Type uK` with `[Field K]` and
`V : Type uV` with `[AddCommGroup V] [Module K V] [FiniteDimensional K V]`.
The universes `uK` and `uV` are independent, and `A : Module.End K V`.
Set `P = eulerPolynomial A`, `S = Langlands.LocalFactor.RegularPoint A`,
`d = P.eval`, and `e = Langlands.LocalFactor.regularEvaluationEquiv A`.
The conjunction consists, in order, of the exact domain clause above, the
forward and inverse input clauses, and

```text
∀ x : S, regularFactorValue A x = value P.eval (e x).
```

The accepted [Euler definitions](../Euler/Definitions.md) define `S` by
`P.eval z ≠ 0` and `regularFactorValue` by inverting the nonzero denominator
unit. The adapter is the identity equivalence after unfolding those subtypes.
The comparison uses the actual evaluator; it does not reinterpret evaluation
of the rational factor at denominator zeros.

## Spectral Euler comparison

`SpectralEulerComparison A q hq` keeps a complex module in its independent
universe `uW`, with `[AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]`,
`A : Module.End ℂ V`, `q : ℝ`, and `hq : 0 < q`.
Set `P = eulerPolynomial A`,
`σ s = (spectralParameter q hq s : ℂ)`, `d = P.eval ∘ σ`,
`S = SpectralRegularPoint A q hq`,
`e = spectralRegularEvaluationEquiv A q hq`, and
`m = spectralToPolynomialPoint A q hq`.
The seven conjuncts are the domain clause

```text
∀ s : ℂ, (∃ x : S, x.val = s) ↔ P.eval (σ s) ≠ 0,
```

followed by the two input clauses for `e`, and these four equations:

```text
∀ x : S, spectralFactorValue A q hq x = value d (e x),
∀ x : S, (m x).val = σ x.val,
∀ x : S, value P.eval (m x) = value d (e x),
∀ x : S, spectralFactorValue A q hq x = value P.eval (m x).
```

Here `σ s` is the published exponential `exp (-s * log q)`, also identified
with `q^(-s)` by `spectralParameter_eq_cpow`. The equivalence preserves the
spectral input; the map produces this substituted polynomial input. No inverse,
injectivity, or surjectivity is asserted for that substitution. The final two
equations expose both generic value preservation and the resulting specialized
value at the polynomial point.

## Reciprocal-entire comparison

`ReciprocalEntireComparison F` uses the same original `F : ReciprocalEntire`.
Set `S = F.RegularPoint`, `d = F.denominator`, and
`e = F.regularEvaluationEquiv`. Its four conjuncts are the exact domain clause,
the two input clauses, and

```text
∀ x : F.RegularPoint, F.eval x = value F.denominator (e x).
```

The source is the accepted [reciprocal-entire API](../Analytic/ReciprocalEntire.md).
Its evaluator constructs a unit from the inverse scalar, whereas the generic
evaluator inverts a denominator unit. This statement compares the resulting
units and does not change either body. The comparison is only at regular
inputs. The object `F`, its entire denominator, its `F.germ`, and its `F.IsPole`
predicate remain unchanged. No rational-function/germ identification or value
at a pole is part of the statement.

## P-adic abelian comparison

`PadicAbelianComparison T χ` retains `p : ℕ`, `[Fact p.Prime]`,
`F : PadicField.{uF} p`, `T : F.TopologicalData`, and
`χ : @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology`.
In this paragraph names such as `RegularPoint` refer to `PadicAbelian`.
Write `a = T.multiplicativeConductor χ`, `π = uniformizerUnit T`,
`P = lPolynomial T χ`, `σ = spectralVariable T`, `d = P.eval ∘ σ`,
`S = {s : ℂ // RegularPoint T π χ a s}`,
`e = regularEvaluationEquiv T χ`, and `m = regularToPolynomialPoint T χ`.
The first of its seven conjuncts is exactly

```text
∀ s : ℂ, RegularPoint T (uniformizerUnit T) χ (T.multiplicativeConductor χ) s
  ↔ (lPolynomial T χ).eval (spectralVariable T s) ≠ 0.
```

This is the domain comparison of the published
`regularPoint_iff_polynomial_ne_zero T χ`. The original arbitrary-conductor
predicate remains `a ≠ 0 ∨ 1 - (χ π : ℂ) * spectralVariable T s ≠ 0`.
Only its specialization at the actual conductor and specified uniformizer is
compared here. This equivalence is not claimed to be definitional unfolding:
the published theorem handles the conductor cases, and the adapter uses it
through `Equiv.subtypeEquivRight`.

The next two conjuncts preserve the input in both directions of `e`. The final
four are

```text
∀ x : S, regularLValue T χ x = value d (e x),
∀ x : S, (m x).val = spectralVariable T x.val,
∀ x : S, value P.eval (m x) = value d (e x),
∀ x : S, regularLValue T χ x = value P.eval (m x).
```

The substituted input is exactly
`exp (-s * log (T.residueCardinality : ℝ))`. The evaluator being compared is
`regularLValue`, with its nonzero certificate supplied by the same published
domain theorem. The totalized scalar representative `lFactor` is not used as
an evaluator at excluded inputs. No inverse to `spectralVariable` is asserted.

## Aggregate, provenance, and boundaries

`ComparisonStatement` universally quantifies each component's full telescope
and conjoins them in the order Euler, spectral Euler, reciprocal-entire,
p-adic abelian. Its four universes `uK`, `uV`, `uW`, and `uF` are independent.
Its type is `Prop`, with the carrier and instance quantifiers inside the
proposition, so the later exact-target proof must not move these assumptions
outside the target.

Worker 64 authored this statement and its documentation. The mathematical
provenance is internal: it compares Worker 12's published adapters directly
with the published specialized formulas. Euler and reciprocal-entire source
work is credited to Worker 20; the [p-adic source](../Abelian/Padic.md) credits
Workers 33 and 20. Their original-source references remain in those imported
modules. The substitution value equations specialize the common interface's
`value_mapInput`; the p-adic domain equation reuses its published theorem.
These dependencies justify the formulation without attributing a new arithmetic
assertion to external literature.

Only this Lean/Markdown pair is added. All original specialized declarations,
including conductors, germs, poles, rational factors, Gamma normalizations,
and epsilon expressions, are retained. No local functional equation or proof
of the comparison family is submitted here.
