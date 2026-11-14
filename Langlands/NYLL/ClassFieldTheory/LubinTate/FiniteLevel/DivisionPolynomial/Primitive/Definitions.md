# The primitive quotient of the standard Lubin–Tate division polynomials

This module extracts exactly M339.014, the definition at line 199 (docstring
line 198, body through line 204) of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean#L198-L204)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The source file's SHA-256 is
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
The whole source file (lines 1–294), including its header, imports, universe
and namespace context and every other declaration, was read directly.

The original is available in the registered source
`external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`.
The project errata lookup contained no entry for either source.

## The definition

The name below is relative to `Langlands.NYLL.LubinTate`. For independent
universes `u v`, a field `K : Type u` with `[Field K]` (both implicit), a
local-field package
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K`,
an element `π : F.valuationSubring` and `n : ℕ`,

```
standardLubinTatePrimitivePolynomial F π n : Polynomial F.valuationSubring :=
  standardLubinTatePolynomialIterate F π n ^ (Nat.card F.residueField - 1) +
    Polynomial.C π
```

Write `q = Nat.card F.residueField` and `f(X) = X ^ q + π X` for the
published standard Lubin–Tate polynomial
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial F π`.
The published iterate
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate F π n` is the
`n`-fold composition `f^[n](X)`, with `f^[0](X) = X`.
The definition is therefore the polynomial
`Qₙ(X) = (f^[n](X)) ^ (q - 1) + π` over the valuation ring of `F`.
The exponent uses natural-number subtraction; since `F.residueField` is a
finite field, `q ≥ 2`, so `q - 1` is the ordinary predecessor, but the
definition itself does not use this fact.

`π` is an arbitrary element of the valuation ring: no uniformizer hypothesis
is assumed, exactly as in the source. The source docstring's phrase
“at level `n + 1`” refers to the intended role of `Qₙ` as the factor of
`f^[n+1]` complementary to `f^[n]`; this module makes no assertion about
roots, irreducibility, Eisenstein properties or Lubin–Tate extensions.

## Exact source correspondence

| Source unit and declaration | Adapted declaration | Type and body |
| --- | --- | --- |
| M339.014, `LubinTate.standardLubinTatePrimitivePolynomial`, line 199 (docstring line 198, body lines 202–204) | `Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial` | `(F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Polynomial F.valuationSubring`; the body, binder order, `noncomputable` marker and docstring are unchanged. |

The source references `LocalField`, `standardLubinTatePolynomialIterate` and
the accessors through `open LocalFieldTheory.DiscreteValuationField` inside
`namespace LubinTate`. Here the same short names resolve, through
`open LocalFieldTheory.DiscreteValuationField` inside
`namespace Langlands.NYLL.LubinTate`, to the published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`, its
abbreviations `LocalField.valuationSubring` and `LocalField.residueField`,
and the published `Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate`.

### M339.015: defining formula by direct unfolding

Source unit M339.015, `standardLubinTatePrimitivePolynomial_formula`
(lines 206–213), asserts
`standardLubinTatePrimitivePolynomial F π n =
standardLubinTatePolynomialIterate F π n ^ (Nat.card F.residueField - 1) +
Polynomial.C π` and is proved by `rfl`. Its right-hand side is literally the
body above, so the equation holds by definitional unfolding of this
declaration (`rfl` or `unfold standardLubinTatePrimitivePolynomial`). No
separate target or theorem is published for M339.015; consumers unfold the
definition directly.

## Import and scope

The sole import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions`,
which supplies the published M339.008 iterate, the M339.001 polynomial, the
`LocalField` package and the polynomial and `Nat.card` APIs used in the
body. The upstream imports
`Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardSeries` and
`Mathlib.Algebra.Polynomial.Monic` are replaced by this focused import; the
definition does not use standard Lubin–Tate power series or series.

Only M339.014 is extracted. The degree, monicity, constant-coefficient and
factorization assertions M339.016–019 are stated, without proofs, in the
separate module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Statements`.
All other source declarations are outside this unit.

## Attribution and complete modification record

The original 2026 copyright, Apache-2.0 release line and author header are
retained verbatim. The existing unmodified
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused. Their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The retained NOTICE has no source-specific entry for this source file, and
the attribution supplement does not list it among the Anthropic-derived files.

Worker 418 made these modifications on 14 November 2026:

- extracted M339.014 and its declaration docstring into this focused module,
  omitting all other source declarations;
- prefixed the declaration namespace with `Langlands.NYLL`, so that the
  namespace is `Langlands.NYLL.LubinTate` and the opened namespace
  `LocalFieldTheory.DiscreteValuationField` resolves to the published
  `Langlands.NYLL` package;
- replaced the two upstream imports by the one published import above;
- dropped `open scoped Polynomial PowerSeries`, which the body does not use;
- closed the namespace with its full name `Langlands.NYLL.LubinTate`;
- replaced the module documentation, added the prominent modification
  notice in the Lean header, and wrote this paired Markdown.

No declaration body, mathematical type, parameter, universe or binder is
changed beyond qualification of names to the published namespace.
