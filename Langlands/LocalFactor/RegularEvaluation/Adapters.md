# Adapters for the three existing regular-evaluation APIs

Worker 12 authored these additive adapters from the published constructions.
No existing specialized definition, statement, proof, or normalization is
modified. The companion comparison statement and its separately reviewed proof
specify preservation of inputs, domains, and unit-valued evaluation.

`Langlands.LocalFactor.regularEvaluationEquiv A` identifies Euler's
`RegularPoint A` with `RegularEvaluation.Point (eulerPolynomial A).eval`.
This is the identity equivalence after transparent unfolding. The polynomial
variable ranges over the arbitrary coefficient field; the carrier universe
of its finite-dimensional module remains independent.

`spectralRegularEvaluationEquiv A q hq` similarly preserves a complex spectral
input `s`. Its denominator is the Euler polynomial composed with
`spectralParameter q hq`. `spectralToPolynomialPoint` then applies that spectral
substitution. This second operation sends `s` to `q^(-s)`, not to `s`, and is
only a map. It supplies no inverse or injectivity claim.

`ReciprocalEntire.regularEvaluationEquiv F` is the identity on the regular
subtype of the original entire denominator. The original object's `germ`,
`germ_meromorphic`, `IsPole`, and `isPole_iff_no_analytic_germ` remain available
unchanged. Its specialized `eval` constructs the unit from the inverse scalar;
the generic evaluator instead inverts a denominator unit. Their comparison
requires unit extensionality and is reserved for the comparison proof. The
existing body is retained. There is no identification of rational functions
with punctured germs, no analyticity condition on a generic denominator, and no
evaluation supplied at poles.

`PadicAbelian.regularEvaluationEquiv T χ` uses Mathlib's
`Equiv.subtypeEquivRight` with the published
`regularPoint_iff_polynomial_ne_zero T χ`. It converts, in both directions,
the subtype satisfying the original `RegularPoint` predicate at the actual
constructed conductor into the support of
`(lPolynomial T χ).eval ∘ spectralVariable T`.
It does not redefine the predicate for arbitrary conductor data or infer that
predicate by definitional equality. The prime, carrier universe, finite p-adic
field, supplied `TopologicalData`, topology on the character, actual conductor,
and specified uniformizer are retained. `regularToPolynomialPoint` sends the
preserved spectral input to `spectralVariable T s`, where the polynomial is
evaluated; this is again a map, not an equivalence.

The original constructions and their source references remain the source of
the arithmetic meaning: Euler and reciprocal-entire were authored by Worker 20;
the p-adic construction credits Workers 33 and 20. These adapters use their
published APIs without copying or changing the constructions. They do not add
an arithmetic L/epsilon identity, a local functional equation, a Gamma
normalization, or a claim about totalized representatives at poles.

## Interface map

The common core is `Langlands.LocalFactor.RegularEvaluation.Definitions`;
all callable adapters below are in `Langlands.LocalFactor.RegularEvaluation.Adapters`.
Declaration names in the table are relative to `Langlands.LocalFactor`.
Every existing declaration named here is intentionally retained with its current body.

| Existing API | Common-domain adapter | Denominator and input | Existing unit evaluator |
| --- | --- | --- | --- |
| `RegularPoint A` | `regularEvaluationEquiv A` | `(eulerPolynomial A).eval`, polynomial input `z : K` | `regularFactorValue A z` |
| `SpectralRegularPoint A q hq` | `spectralRegularEvaluationEquiv A q hq` | `(eulerPolynomial A).eval` composed with `s ↦ (spectralParameter q hq s : ℂ)`, spectral input `s : ℂ` | `spectralFactorValue A q hq s` |
| `ReciprocalEntire.RegularPoint F` | `ReciprocalEntire.regularEvaluationEquiv F` | `F.denominator`, complex input `z` | `F.eval z` |
| `{s // PadicAbelian.RegularPoint T (PadicAbelian.uniformizerUnit T) χ (T.multiplicativeConductor χ) s}` | `PadicAbelian.regularEvaluationEquiv T χ` | `(PadicAbelian.lPolynomial T χ).eval` composed with `PadicAbelian.spectralVariable T`, spectral input `s` | `PadicAbelian.regularLValue T χ s` |

The common evaluator for a row is `RegularEvaluation.value` at its indicated
denominator and the image of the original regular input under the adapter.
The separate comparison statement and proof will record equality with the unit
in the final column. Both spectral rows also expose a map to the polynomial
support: `spectralToPolynomialPoint` and `PadicAbelian.regularToPolynomialPoint`.
They apply `RegularEvaluation.mapInput` to the indicated substitution. The
underlying polynomial input is the substituted value, while the corresponding
equivalence preserves the original spectral input.

The required module migration has the following map; it does not rename any
of the declarations used above. Old paths remain paired compatibility imports.

| Original module | Canonical module after the path migration |
| --- | --- |
| `Langlands.LocalFactor.Euler` | `Langlands.LocalFactor.Euler.Definitions` |
| `Langlands.LocalFactor.ReciprocalEntire` | `Langlands.LocalFactor.Analytic.ReciprocalEntire` |
| `Langlands.LocalFactor.PadicAbelian` | `Langlands.LocalFactor.Abelian.Padic` |

The adapters import the canonical modules published in Library
`d7cf4d2d2f040f4dfa5ab22d869d51196351d821`, the refreshed workspace base.
Every existing file at that base is retained byte for byte. The subsequent
Library commit `3b5205fa6ae98b1b2f57b8bfc33e99d78771f240` adds only public
documentation and does not change any Lean module.

The comparison statement is a separate contribution, followed by an
exact-target proof against its published declaration. This construction does
not claim that those comparisons have already been accepted or published.

## Validation scope

Development validation used Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` through the project's incremental
Lake service. The two new modules compile with no errors or warnings.
A private aggregate imports all 385 Lean modules of the refreshed base and
both new modules; its Lake build also completes with no errors or warnings.
All 387 public Lean files have nonempty same-stem Markdown, and every existing
base file remains byte-identical.

The aggregate prints the unapplied declaration types, with universes and
explicit parameters, and axiom closures for all twelve new declarations.
The generic input, substituted input, and value universes remain independent;
Euler's coefficient and module universes remain independent. The p-adic
adapters retain the prime instance, field carrier universe, supplied topology,
character, actual conductor, and specified uniformizer. Axiom closures contain
only `propext`, `Classical.choice`, and `Quot.sound`, or are empty.
These are development checks, not independent mathematical acceptance or
publication of the separately required comparison statement and proof.
