# Proof of the regular-evaluation comparison with local-factor adapters

This module proves the published proposition
`Langlands.LocalFactor.RegularEvaluation.ComparisonStatement` from
[ComparisonStatement](ComparisonStatement.md). The closing theorem is

```lean
theorem comparisonStatement : ComparisonStatement.{uK, uV, uW, uF}
```

Its type is exactly the published proposition, with its four independent
universes `uK`, `uV`, `uW`, `uF`. All carrier, instance, object, and hypothesis
quantifiers stay inside that proposition; the theorem has no hypotheses of its
own. The module imports the published statement module and adds no definitions.
It changes no published Lean/Markdown pair.

## Decomposition

The proof has four component theorems, one for each conjunct of the statement.
`comparisonStatement` conjoins them in the published order. It introduces each
component's telescope, including the instance arguments, and applies the
component theorem.

| Conjunct | Component theorem | Arguments |
| --- | --- | --- |
| `EulerComparison A` | `eulerComparison` | `K : Type uK` with `[Field K]`, `V : Type uV` with its finite-dimensional module structure, `A` |
| `SpectralEulerComparison A q hq` | `spectralEulerComparison` | `V : Type uW` with its finite-dimensional complex module structure, `A`, `q`, `hq : 0 < q` |
| `ReciprocalEntireComparison F` | `reciprocalEntireComparison` | `F : ReciprocalEntire` |
| `PadicAbelianComparison T χ` | `padicAbelianComparison` | `p`, `[Fact p.Prime]`, `F : PadicField.{uF} p`, `T`, `χ` |

The names below abbreviate the published declarations exactly as in the
statement's Markdown. For a denominator `d`, `Point d` is the support subtype
and `value d x = (Units.mk0 (d x.val) x.property)⁻¹`.

## Domain clauses

For the polynomial Euler, spectral Euler, and reciprocal-entire components,
the domain clause is `(∃ x : S, x.val = z) ↔ d z ≠ 0`. In each case the
specialized subtype `S` is defined as `{z // d z ≠ 0}`:
`RegularPoint A` by `(eulerPolynomial A).eval z ≠ 0`, `SpectralRegularPoint A q hq`
by `(eulerPolynomial A).eval (spectralParameter q hq s : ℂ) ≠ 0`, and
`F.RegularPoint` by `F.denominator z ≠ 0`. The forward direction destructs the
witness `x` with `x.val = z` and returns its subtype property `x.2`. The reverse
direction builds the witness `⟨z, h⟩`, whose value is `z` by `rfl`.

The p-adic domain clause is not proved by unfolding. It is the published theorem
`PadicAbelian.regularPoint_iff_polynomial_ne_zero T χ`, used unchanged. Its
predicate is the original `RegularPoint` at the actual conductor
`T.multiplicativeConductor χ` and the uniformizer `uniformizerUnit T`.
The arbitrary-conductor `RegularPoint` predicate itself is not used elsewhere.

## Input clauses

Each component has two input clauses, `(e x).val = x.val` and
`(e.symm y).val = y.val`, for its adapter `e`. The Euler, spectral Euler, and
reciprocal-entire adapters are `Equiv.refl _`. Both clauses therefore hold by
`rfl`. The p-adic adapter is `Equiv.subtypeEquivRight` along
`regularPoint_iff_polynomial_ne_zero T χ`. In both directions this Mathlib
equivalence keeps the underlying complex number and transports only the
membership proof, so both clauses again hold by `rfl`.

## Unit equalities

All value equalities are equalities in `Kˣ` or `ℂˣ`.

- **Euler.** `regularFactorValue A x` is `(Units.mk0 ((eulerPolynomial A).eval x.1) x.2)⁻¹`.
  Since the adapter is the identity, `value (eulerPolynomial A).eval (e x)`
  reduces to the same expression, with the same denominator and nonzero
  certificate. The equality holds by `rfl`.
- **Spectral Euler.** `spectralFactorValue A q hq x` is by definition
  `regularFactorValue A ⟨spectralParameter q hq x.1, x.2⟩`. The generic side
  `value ((eulerPolynomial A).eval ∘ σ) (e x)` unfolds `Function.comp` to the
  same inverse unit, so the first value clause holds by `rfl`. The map
  `m = spectralToPolynomialPoint A q hq` is `mapInput` applied after the
  identity adapter. Its underlying input `(m x).val = σ x.val` holds by `rfl`.
  The equation `value (eulerPolynomial A).eval (m x) = value d (e x)` is the
  published `value_mapInput` lemma. The last equation,
  `spectralFactorValue A q hq x = value (eulerPolynomial A).eval (m x)`, is again
  definitional and holds by `rfl`. No inverse of spectral substitution is used
  or asserted.
- **Reciprocal entire.** The bodies differ: `F.eval x` is
  `Units.mk0 (F.denominator x.val)⁻¹ _`, a unit built from the inverse scalar,
  whereas `value F.denominator (e x)` inverts the unit built from the
  denominator. The proof applies `Units.ext` and rewrites with the published
  `ReciprocalEntire.coe_eval` and `RegularEvaluation.coe_value`. The goal is then
  `(F.denominator x.val)⁻¹ = (F.denominator (e x).val)⁻¹`. It closes by `rfl`
  because `e` is the identity. Only `F.eval` at regular inputs is compared;
  `F`, its denominator, its `germ`, and its `IsPole` predicate are untouched.
- **P-adic abelian.** `regularLValue T χ x` is
  `(Units.mk0 ((lPolynomial T χ).eval (spectralVariable T x.val)) c)⁻¹`, where the
  certificate `c` is `(regularPoint_iff_polynomial_ne_zero T χ x.val).mp x.property`.
  The generic side `value ((lPolynomial T χ).eval ∘ spectralVariable T) (e x)`
  has the same denominator and, by the definition of `Equiv.subtypeEquivRight`,
  the same certificate. The first value clause therefore holds by `rfl`. For
  `m = regularToPolynomialPoint T χ`, which is `mapInput` after `e`, the input
  clause `(m x).val = spectralVariable T x.val` holds by `rfl`. The clause
  `value (lPolynomial T χ).eval (m x) = value d (e x)` is `value_mapInput`. The
  final clause `regularLValue T χ x = value (lPolynomial T χ).eval (m x)` is
  definitional and holds by `rfl`.

The proof uses no tactic automation beyond `refine`, `rintro`, `intro`,
`exact`, `apply`, `rw`, and `rfl`. It does not use `lFactor`, functional
equations, Gamma factors, epsilon factors, or any change of conductor
convention.

## Provenance and authorship

The mathematical content is internal. It consists of unfolding Worker 12's
published [common interface](Definitions.md) and [adapters](Adapters.md) against
the published specialized constructions. These are the
[Euler definitions](../Euler/Definitions.md) and the
[reciprocal-entire API](../Analytic/ReciprocalEntire.md), both by Worker 20, and
the [p-adic abelian factor](../Abelian/Padic.md), by Workers 33 and 20. Their
original-literature citations remain in those modules. Worker 64 authored the
target statement, and Worker 82 checked its scope. The proof reuses the
published lemmas `value_mapInput`, `coe_value`, `ReciprocalEntire.coe_eval`, and
`PadicAbelian.regularPoint_iff_polynomial_ne_zero`, together with Mathlib's
`Units.ext`.

The proof route follows the feasibility guidance that Worker 12 gave in the
task context. Worker 85 wrote and checked this Lean proof; no unpublished proof
material by another author is reused.

## Validation

Development checks used environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). The module
compiles with no errors or warnings. Inspection of `comparisonStatement` reports
a theorem with level parameters `uK`, `uV`, `uW`, `uF`. Its axiom closure is
exactly `propext`, `Classical.choice`, and `Quot.sound`, which come from the
imported definitions. These development checks are not independent acceptance;
the staged candidate's Lake build, kernel replay, exact-target check, and review
are separate.
