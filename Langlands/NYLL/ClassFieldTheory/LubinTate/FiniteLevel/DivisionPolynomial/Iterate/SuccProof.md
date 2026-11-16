# Successor recursion for standard Lubin–Tate polynomial iterates (M339.010)

`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_succ` proves
the fully applied published target
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_succStatement F π n`.
The theorem retains independent universes `u v`, implicit
`{K : Type u} [Field K]`, and explicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
`π : F.valuationSubring` and `n : ℕ`.

For every natural number `n`, the equality is

```text
standardLubinTatePolynomialIterate F π (n + 1) =
  (standardLubinTatePolynomial F π).comp
    (standardLubinTatePolynomialIterate F π n).
```

The composition on the right substitutes the `n`-fold iterate into the
standard polynomial. The element `π` is arbitrary in the valuation subring;
there is no uniformizer or additional finiteness hypothesis.

## Implemented proof

Unfold the proposition-valued target. The published iterate definition is
`(standardLubinTatePolynomial F π).comp^[n] Polynomial.X`. Rewrite the
successor iterate by this definition and then apply
`Function.iterate_succ_apply'`, which expresses a successor function iterate
as one outer application after the preceding iterate. The resulting equality
is reflexive after unfolding the remaining occurrence of the iterate
definition, so `rfl` closes the goal.

The proof uses the imported statement and its published definitions directly.
It needs no local helper, induction, or theorem about polynomial degree,
monicity or roots. Its only import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Statements`.
The target pair and all imported pairs are preserved.

## Original source and modifications

Naganori Yamaguchi, NYLL ClassFieldTheory commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`,
M339.010: docstring lines 144–145, declaration line 146, type lines 147–150
and proof lines 151–153. Source file SHA-256:
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
Registered sources:
`external-lean-reuse-snapshots-2026-10-21` (content hash
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (content hash
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The source theorem name, telescope, docstring and three-line rewrite proof
are retained. The namespace is prefixed with `Langlands.NYLL`. Its expanded
equality type is replaced by the fully applied imported statement, with an
initial `unfold` step exposing that equality. The source's broader imports
are replaced by the focused statement import; the unused
`open scoped Polynomial PowerSeries` is omitted. Module documentation and
the modification notice are new. No other source declaration is copied.

The Lean header retains the original copyright, Apache-2.0 license notice
and authorship. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged.
