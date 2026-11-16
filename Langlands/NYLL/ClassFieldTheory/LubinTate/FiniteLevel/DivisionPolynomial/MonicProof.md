# Monicity of the standard Lubin–Tate polynomial (M339.007)

This module proves the published proposition
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial_monicStatement`
from [DegreeStatements](DegreeStatements.md), using the theorem
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial_monic`.
Its complete telescope has independent universes `u v`, implicit
`{K : Type u} [Field K]`, and explicit
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)`
and `(π : F.valuationSubring)`. The declared result type is the fully
applied imported proposition `standardLubinTatePolynomial_monicStatement F π`.
There are no additional hypotheses.

For `q = Nat.card F.residueField`, the conclusion says that
`X ^ q + Polynomial.C π * X`, over `F.valuationSubring`, is monic.
The element `π` is arbitrary; the proof does not require a uniformizer.
The package `F` already includes finiteness of its residue field.

## Implemented proof

The proof unfolds the imported target and the published polynomial definition.
`Polynomial.monic_X_pow` supplies monicity of `X ^ q`, and
`Polynomial.Monic.add_of_left` reduces the conclusion to the assertion that
the added term has strictly smaller degree.

`Polynomial.degree_C_mul_X_le π` bounds the degree of `C π * X` by `1`,
including when `π = 0`. The residue field is a finite nontrivial field, so
`Finite.one_lt_card` gives `1 < q` using its existing instances.
`Polynomial.degree_X_pow` computes the degree of `X ^ q`, and
`exact_mod_cast` transports the natural-number inequality to polynomial
degrees. These inequalities finish the monicity proof.

The module imports only the existing target module and
`Mathlib.Algebra.Polynomial.Monic`. It adds one theorem and no definitions,
instances or helper declarations. The published target pair and its imports
are unchanged. No natural-degree, iterate or uniformizer result is asserted.

## Source and modifications

The proof is adapted from Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`,
lines 116–128](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean#L116-L128),
declaration `LubinTate.standardLubinTatePolynomial_monic`, at commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The source file's SHA-256 is
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
It is available in registered source
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
under `n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No project erratum for these sources was found.

Worker 775 made the following modifications on 16 November 2026:

- extracted only M339.007 into this focused proof module;
- prefixed the namespace with `Langlands.NYLL`, preserving the original
  universes and binders;
- replaced the theorem's expanded conclusion with the fully applied published
  statement and added its unfolding; the remaining proof follows the source;
- replaced the source's standard-series import with the published target
  module, retained the Mathlib monicity import, and omitted unused scoped
  notation openings;
- replaced the module documentation, prefixed the docstring with the unit
  number, added the modification notice, and wrote this paired Markdown.

The original copyright, author and Apache-2.0 release header is preserved.
The existing [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
