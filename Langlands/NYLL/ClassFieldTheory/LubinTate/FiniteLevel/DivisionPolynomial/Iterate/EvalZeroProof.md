# Standard Lubin–Tate polynomial iterates vanish at zero (M339.013)

`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_eval_zero`
proves the imported proposition
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_eval_zeroStatement F π n`.
The theorem retains independent universes `u v`, implicit
`{K : Type u} [Field K]`, and explicit arguments
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
`π : F.valuationSubring` and `n : ℕ`. It states
`(standardLubinTatePolynomialIterate F π n).eval 0 = 0` in the valuation
subring. There are no additional hypotheses: `π` is arbitrary, and the
finite residue-field instance is supplied by `F`. The source `@[simp]`
attribute is retained.

The module imports the published `Iterate.Statements` module by Lean name
and preserves its Lean/Markdown pair and all imports. It introduces only
the named proof; the polynomial, its iterates and the target proposition
are the published definitions.

## Implemented proof

After exposing the proposition as the evaluation equality, induct on `n`.
At level zero the iterate definition gives `Polynomial.X`, whose evaluation
at zero simplifies to zero.

In the successor case, the local equality `hsucc` unfolds the iterate
definition and uses `Function.iterate_succ_apply'` to express the next
iterate as the standard polynomial composed with the preceding iterate.
`Polynomial.eval_comp` and the induction hypothesis then reduce the goal
to evaluation of the standard polynomial at zero. That polynomial is
`X ^ q + C π * X`, with `q = Nat.card F.residueField`.
The inherited finite, nontrivial residue field gives `1 < q` by
`Finite.one_lt_card`, hence `q ≠ 0`; simplification therefore evaluates
both summands to zero. The local successor equality is a necessary
definitional proof step and introduces no public helper declaration.

## Original source and modifications

Naganori Yamaguchi, NYLL ClassFieldTheory commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`,
M339.013: documentation and attribute at lines 182–183, declaration at
line 184, type at lines 185–186 and proof at lines 187–196.
The file SHA-256 is
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
The readable pinned source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The existing errata filenames contain no entry for NYLL or these sources.

Modifications by Worker 311:

- Extract only M339.013 into the task's focused `EvalZeroProof` module.
- Prefix the source namespace `LubinTate` with `Langlands.NYLL`.
- Replace the displayed equality in the theorem type with the fully applied
  imported `standardLubinTatePolynomialIterate_eval_zeroStatement F π n`;
  `change` exposes the same equality inside the proof.
- Replace the upstream formal-series and polynomial monicity imports with
  the published `Iterate.Statements` import, which supplies the definitions
  and evaluation lemmas used here.
- Replace the source successor-recursion theorem invocation with the local
  equality `hsucc`, proved by the source M339.010 route from the iterate
  definition. The induction, composition evaluation, cardinality argument
  and simplification follow M339.013.
- Replace the source module documentation and omit its unused
  `open scoped Polynomial PowerSeries`.

The original copyright, Apache-2.0 notice and author attribution are retained
in the Lean header, together with a modification notice. Existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain unchanged.
