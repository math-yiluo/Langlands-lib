# Natural degree of the primitive Lubin–Tate quotient polynomial

This module proves
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial_natDegreeStatement`
by declaring
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial_natDegree`.
Its declared type is the fully applied imported target
`standardLubinTatePrimitivePolynomial_natDegreeStatement F π n`.

The binders are implicit `{K : Type u} [Field K]` and explicit
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)`,
`(π : F.valuationSubring)` and `(n : ℕ)`, with independent universes `u v`.
There is no additional hypothesis. In particular, `π` need not be a
uniformizer. Finiteness of the residue field comes from the existing
`LocalField` package.

Write `q = Nat.card F.residueField`,
`f = standardLubinTatePolynomial F π = X ^ q + C π * X`, and
`fₙ = standardLubinTatePolynomialIterate F π n`, the `n`-fold
compositional iterate starting at `X`. The target states

```text
natDegree (fₙ ^ (q - 1) + C π) = (q - 1) * q ^ n.
```

## Implemented proof

After unfolding the target, the proof obtains two local facts directly from
the published definitions:

1. `natDegree f = q`. The term `C π * X` has natural degree at most `1`,
   whereas `X ^ q` has natural degree `q`, and `Finite.one_lt_card` gives
   `1 < q`. Thus `Polynomial.natDegree_add_eq_left_of_natDegree_lt`
   computes the degree of the sum.
2. `natDegree fₙ = q ^ n`. Unfolding the iterate and applying
   `Polynomial.natDegree_iterate_comp` gives
   `(natDegree f) ^ n * natDegree X`, which reduces to `q ^ n`.

The same cardinality inequality gives `0 < q - 1`, while
`Nat.pow_pos Nat.card_pos` gives `0 < q ^ n`. Therefore
`0 < (q - 1) * q ^ n`. Unfolding the primitive polynomial and using
`Polynomial.natDegree_pow` shows that its power term has this positive
natural degree. Since `Polynomial.natDegree_C` gives natural degree `0`
for `C π`, the strict-degree sum lemma applies again and proves the target.
This includes `n = 0` and `π = 0` without separate cases.

The two intermediate degree facts are local to this proof. They do not
introduce the canonical standard-polynomial or iterate-degree declarations,
and the proof imports no unpublished prerequisite.

## Source and modifications

The source is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean#L215-L235)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, SHA-256
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
The whole source file, lines 1–294, was read directly from the registered
source `external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`. No corresponding project
erratum was found.

The final degree argument is source unit M339.016, lines 215–235.
The local standard-polynomial calculation follows M339.006, lines 100–114,
and the local iterate calculation follows M339.011, lines 155–163.
These are the only mathematical source units used in this proof.

Worker 774 made the following modifications on 16 November 2026:

- extracted M339.016, preserving its complete universe and parameter
  telescope, and prefixed the namespace with `Langlands.NYLL`;
- used the fully applied published proposition as the theorem's explicit
  type and unfolded it at the beginning of the proof;
- replaced calls to the source degree theorems by local facts containing
  their small calculations, without adding separate declarations;
- imported the existing primitive target module and
  `Mathlib.Algebra.Polynomial.Degree.Lemmas`, replacing the upstream
  power-series and monicity imports;
- omitted unrelated declarations and unused scoped opens, replaced the
  module documentation, added the modification notice, and wrote this
  paired Markdown.

The original copyright, author and Apache-2.0 header are retained. The
existing [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The target, its paired Markdown, and all its imports are unchanged.
