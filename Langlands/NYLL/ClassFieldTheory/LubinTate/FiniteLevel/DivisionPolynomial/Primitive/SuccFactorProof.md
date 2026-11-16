# Successor factorization for standard Lubin–Tate polynomial iterates (M339.019)

`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_succ_factor`
proves the fully applied published target
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_succ_factorStatement F π n`.
The theorem retains independent universes `u v`, implicit
`{K : Type u} [Field K]`, and explicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
`π : F.valuationSubring` and `n : ℕ`.

Write `q = Nat.card F.residueField`, `f = standardLubinTatePolynomial F π`,
`A = standardLubinTatePolynomialIterate F π n`, and
`Qₙ = standardLubinTatePrimitivePolynomial F π n`. The conclusion is

```text
standardLubinTatePolynomialIterate F π (n + 1) = A * Qₙ.
```

All polynomials have coefficients in `F.valuationSubring`. The element `π`
is arbitrary in that ring. The theorem adds no uniformizer or finiteness
hypothesis; finiteness of the residue field is already part of `F`.

## Implemented proof

Unfold the proposition-valued target. The residue field is a finite field,
so `Finite.one_lt_card` gives `1 < q`, from which the proof derives
`hq : q ≠ 0`.

Rewrite the successor iterate with the published
`standardLubinTatePolynomialIterate_succ`, then unfold the standard
polynomial and the primitive polynomial. Simplifying polynomial
composition with `Polynomial.add_comp`, `Polynomial.pow_comp`,
`Polynomial.X_comp`, `Polynomial.mul_comp` and `Polynomial.C_comp` yields

```text
A ^ q + Polynomial.C π * A =
  A * (A ^ (q - 1) + Polynomial.C π).
```

Rewrite `A ^ q` as `A ^ (q - 1) * A` using `← pow_sub_one_mul hq`.
The `ring` tactic closes the resulting commutative-ring identity. The
subtraction in `q - 1` is natural subtraction; `hq` justifies the power
identity. No local helper declaration is needed.

The proof imports the published target from
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Statements`,
the published recursion theorem from
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.SuccProof`,
and `Mathlib.Tactic.Ring`. The target pair and all imported pairs are
preserved.

## Original source and modifications

Naganori Yamaguchi, NYLL ClassFieldTheory commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean#L273-L290),
M339.019: docstring lines 273–274, declaration line 275, type lines
276–279 and proof lines 280–290. Source file SHA-256:
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
Registered sources:
`external-lean-reuse-snapshots-2026-10-21` (content hash
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (content hash
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable entry was found in the project's `notes/errata/`.

The source theorem name, telescope, docstring and proof after the initial
target unfolding are retained. The namespace is prefixed with
`Langlands.NYLL`. The source equality type is replaced by the fully applied
imported statement, and the proof begins by unfolding that statement.
The source's broader imports are replaced by the focused imports above;
the unused `open scoped Polynomial PowerSeries` is omitted. Module
documentation, the modification notice and this Markdown are new. No
other source declaration is copied.

The Lean header retains the original copyright, Apache-2.0 license notice
and authorship. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged. The attribution supplement does not
list this source file among the Anthropic-derived files.
