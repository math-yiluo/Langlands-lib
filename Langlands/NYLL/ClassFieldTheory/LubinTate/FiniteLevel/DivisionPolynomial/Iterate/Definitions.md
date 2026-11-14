# Standard Lubin–Tate polynomial iterates (M339.008)

`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate` is a
noncomputable definition with independent universes `u v`, implicit
`{K : Type u} [Field K]`, and explicit arguments
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
`π : F.valuationSubring` and `n : ℕ`. Its value is a polynomial over the
valuation subring of `F`:

```
(standardLubinTatePolynomial F π).comp^[n] Polynomial.X
```

That is, starting from `X`, the function `g ↦ f.comp g` (with
`f = standardLubinTatePolynomial F π = X ^ q + C π * X`,
`q = Nat.card F.residueField`) is applied `n` times. Since
`f.comp g = f(g)`, the value is the `n`-fold compositional iterate
`f(f(⋯ f(X)))`. The polynomial `f` is the published M339.001 definition
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial`, imported by its
Lean name. `F` is the shared LocalField package, not a copy.

No hypothesis on `π` is added: `π` need not be a uniformizer, as in the
source. The definition proves nothing about degree, monicity, roots or
factorization. Those are separate statements (see the sibling
`Statements` pair) or later source units.

## M339.009 (zero iterate)

The source theorem `standardLubinTatePolynomialIterate_zero`
(line 139) states `standardLubinTatePolynomialIterate F π 0 = Polynomial.X`.
This is direct definitional reduction: `Nat.iterate _ 0 x` reduces to `x`.
So `rfl` proves it from this definition, with no further theorem needed.
A private check with `lean_check` confirmed this `rfl` example. As the
task context records, no separate M339.009 target or theorem is part of
this unit.

## Original source and modifications

Naganori Yamaguchi, NYLL ClassFieldTheory commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`,
M339.008 at lines 130–135 (docstring 130–131; declaration starting at line 132).
Source file SHA-256:
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21` (content hash
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (content hash
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The declaration keeps the source name, docstring, universe parameters,
`variable {K : Type u} [Field K]` context, binder order and explicitness,
result type and body. Modifications:

- Namespace: source `LubinTate` becomes `Langlands.NYLL.LubinTate`. The source
  `open LocalFieldTheory.DiscreteValuationField` resolves inside it to the
  published `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`.
- Extraction: only this definition is taken from the source file, in its own
  focused module.
- Imports: the source imports `Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardSeries`
  and `Mathlib.Algebra.Polynomial.Monic`. This module has two focused imports
  instead:
  - `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Definitions`,
    the published M339.001 module defining `standardLubinTatePolynomial`. It
    brings in the shared LocalField package and `Mathlib.Algebra.Polynomial.Basic`.
  - `Mathlib.Algebra.Polynomial.Eval.Defs`, which defines `Polynomial.comp`.

  The standard series is not used.
- The unused `open scoped Polynomial PowerSeries` is dropped, and the module
  documentation is new.
- Omitted source units: M339.001–.007 (published separately or owned by Task
  6126), M339.009 (definitional; see above), M339.010–.013 (statements in the
  sibling `Statements` pair), and M339.014 onward.

The Lean header keeps the original copyright, Apache-2.0 notice and
authorship, and adds a modification line. The source file is not one of the
Anthropic-derived files listed in the supplement's
`Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md`. Licensing and attribution
stay in the existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This unit does not change either file.
