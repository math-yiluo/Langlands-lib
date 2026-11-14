# Targets for the primitive Lubin–Tate quotient polynomial

This module states, as proposition-valued definitions without proofs, the
four source theorems M339.016–019 of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean#L215-L290)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, lines 215–290.
The source file's SHA-256 is
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
The whole source file (lines 1–294) was read directly.

The original is available in the registered source
`external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`.
The project errata lookup contained no entry for either source.

## Setting and notation

All names below are relative to `Langlands.NYLL.LubinTate`. Each target
has implicit `{K : Type u} [Field K]` and explicit
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)`,
`(π : F.valuationSubring)` and `(n : ℕ)`, with independent universes
`u v`, and returns `Prop`. These are exactly the source theorems' binders.
No hypothesis on `π` (in particular no uniformizer hypothesis) is added.

Write `q = Nat.card F.residueField` (natural-number cardinality of the
finite residue field), `f(X) = X ^ q + π X` for the published
`standardLubinTatePolynomial F π`, `f^[n]` for the published
`standardLubinTatePolynomialIterate F π n` (the `n`-fold composition,
`f^[0] = X`), and `Qₙ = (f^[n]) ^ (q - 1) + π` for the published
`standardLubinTatePrimitivePolynomial F π n`. All polynomials are over the
valuation ring `F.valuationSubring`.

## The four targets

| Source unit, theorem and lines | Target | Proposition |
| --- | --- | --- |
| M339.016, `LubinTate.standardLubinTatePrimitivePolynomial_natDegree`, line 216 (docstring 215, statement 216–220) | `standardLubinTatePrimitivePolynomial_natDegreeStatement` | `(standardLubinTatePrimitivePolynomial F π n).natDegree = (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n` |
| M339.017, `LubinTate.standardLubinTatePrimitivePolynomial_monic`, line 238 (docstring 237, statement 238–240) | `standardLubinTatePrimitivePolynomial_monicStatement` | `(standardLubinTatePrimitivePolynomial F π n).Monic` |
| M339.018, `LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero`, line 263 (docstring 261, `@[simp]` 262, statement 263–265) | `standardLubinTatePrimitivePolynomial_coeff_zeroStatement` | `(standardLubinTatePrimitivePolynomial F π n).coeff 0 = π` |
| M339.019, `LubinTate.standardLubinTatePolynomialIterate_succ_factor`, line 275 (docstring 273–274, statement 275–279) | `standardLubinTatePolynomialIterate_succ_factorStatement` | `standardLubinTatePolynomialIterate F π (n + 1) = standardLubinTatePolynomialIterate F π n * standardLubinTatePrimitivePolynomial F π n` |

In words:

- **M339.016**: `Qₙ` has natural degree `(q - 1) · qⁿ`.
- **M339.017**: `Qₙ` is monic (leading coefficient `1`).
- **M339.018**: the constant coefficient of `Qₙ` is `π`.
- **M339.019**: `f^[n+1] = f^[n] · Qₙ`.

Each proposition is the source theorem's conclusion, verbatim after name
qualification, with the same binders. The subtraction `q - 1` is natural
subtraction, as in the source. Each target is a `def` returning `Prop`
named by appending `Statement` to the source theorem name; it asserts but
does not prove the conclusion. Proofs are separate later units.

## Relation to M339.014 and M339.015

`standardLubinTatePrimitivePolynomial` is the published M339.014
definition in
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions`.
Source unit M339.015, `standardLubinTatePrimitivePolynomial_formula`
(lines 206–213), is the `rfl` equation between that definition and its
body; it holds by direct definitional unfolding and has no target here.

## Import and scope

The imports are the published M339.014 module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions`
(which transitively supplies the M339.008 iterate, the M339.001 polynomial
and the `LocalField` package) and `Mathlib.Algebra.Polynomial.Degree.Defs`
for `Polynomial.natDegree` and `Polynomial.Monic`. The upstream imports
`Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardSeries` and
`Mathlib.Algebra.Polynomial.Monic` are replaced by these focused imports;
the targets do not mention power series.

Only the statements of M339.016–019 are extracted. The source proofs, which
use the degree, monicity, successor and evaluation-at-zero facts
M339.006/.007/.010–.013 about the polynomial and its iterates, are not part
of this unit.

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

- recast the four source theorems as `def … : Prop` targets whose bodies
  are the source conclusions, named with the suffix `Statement`, and
  omitted their proofs;
- omitted the `@[simp]` attribute of M339.018, which applies only to a
  theorem;
- adapted the docstrings by prefixing the source unit numbers;
- prefixed the declaration namespace with `Langlands.NYLL`, so that the
  namespace is `Langlands.NYLL.LubinTate` and the opened namespace
  `LocalFieldTheory.DiscreteValuationField` resolves to the published
  `Langlands.NYLL` package;
- replaced the two upstream imports by the two focused imports above;
- dropped `open scoped Polynomial PowerSeries`, which the statements do not
  use;
- closed the namespace with its full name `Langlands.NYLL.LubinTate`;
- replaced the module documentation, added the prominent modification
  notice in the Lean header, and wrote this paired Markdown.

No binder, universe, hypothesis or mathematical conclusion is changed
beyond qualification of names to the published namespace.
