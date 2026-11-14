# Degree and monicity targets for the standard Lubin–Tate polynomial (M339.006–007)

This module states source units M339.006 and M339.007 of Naganori
Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean#L100-L128)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` as propositions,
without proofs. The source file's SHA-256 is
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.

The original is in the registered source
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The project has no errata note for either source.

## Statements

Both declarations are `def`s returning `Prop`, in namespace
`Langlands.NYLL.LubinTate`, with independent universe parameters `u v`,
implicit `{K : Type u} [Field K]`, and explicit
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)`
and `(π : F.valuationSubring)`. They use the published definition
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial F π`, the polynomial
`X ^ q + π * X` over the valuation ring, with `q = Nat.card F.residueField`.

- `standardLubinTatePolynomial_natDegreeStatement F π` asserts
  `(standardLubinTatePolynomial F π).natDegree = Nat.card F.residueField`:
  the polynomial has natural degree `q`.
- `standardLubinTatePolynomial_monicStatement F π` asserts
  `(standardLubinTatePolynomial F π).Monic`: its leading coefficient is `1`.

`π` is an arbitrary element of the valuation ring; no uniformizer
hypothesis is made, as in the source. Neither proposition adds a finiteness
hypothesis; the source proofs obtain `1 < q` from the package's
`residueFinite` instance. No hypothesis is added or removed relative to the
source theorems.

These are targets only. This module proves neither proposition. Separately
accepted proofs are still required.

## Exact source correspondence

| Source unit and declaration | Adapted declaration | Proposition |
| --- | --- | --- |
| M339.006, theorem `LubinTate.standardLubinTatePolynomial_natDegree`, line 101 (type lines 100–104, proof lines 105–114) | `Langlands.NYLL.LubinTate.standardLubinTatePolynomial_natDegreeStatement` | `(standardLubinTatePolynomial F π).natDegree = Nat.card F.residueField` |
| M339.007, theorem `LubinTate.standardLubinTatePolynomial_monic`, line 117 (type lines 116–119, proof lines 120–128) | `Langlands.NYLL.LubinTate.standardLubinTatePolynomial_monicStatement` | `(standardLubinTatePolynomial F π).Monic` |

In each case the source theorem's binders, universes and conclusion become
the `def`'s binders, universes and `Prop`-valued body unchanged, and the name
gains the suffix `Statement`. The docstrings keep the source wording, with the
unit number prefixed.

## Namespace, imports and API

- Namespace: `LubinTate` becomes `Langlands.NYLL.LubinTate`. The source's
  `open LocalFieldTheory.DiscreteValuationField` resolves, within the new
  namespace, to the published
  `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`.
- Imports: the source imports
  `Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardSeries` and
  `Mathlib.Algebra.Polynomial.Monic`. These statements need neither the
  standard series nor the monicity lemmas, so the imports are replaced by:
  - `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Definitions`
    (the definition M339.001);
  - `Mathlib.Algebra.Polynomial.Degree.Defs` (`Polynomial.natDegree` and
    `Polynomial.Monic`).
- The source's `open scoped Polynomial PowerSeries` is dropped, since
  neither notation is used.
- API: two new declarations,
  `Langlands.NYLL.LubinTate.standardLubinTatePolynomial_natDegreeStatement`
  and `Langlands.NYLL.LubinTate.standardLubinTatePolynomial_monicStatement`.
  No existing Library declaration is changed.

## Scope

Only the statements of M339.006 and M339.007 are extracted. Their source
proofs, the formula, evaluation and power-series correspondences
(M339.002–005), and the iterate and factor material (M339.008 onward) are
excluded.

## Attribution and complete modification record

The original 2026 copyright, Apache-2.0 release line and author header are
retained verbatim in the Lean file. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused; their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The NOTICE has no source-specific entry for this file, and the supplement's
`Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` does not list it as derived
from another project.

Worker 416 made these modifications on 14 November 2026:

- extracted the types of M339.006 and M339.007 into this focused module and
  turned each theorem into a `def` returning `Prop`, named with the suffix
  `Statement`, omitting the source proofs;
- prefixed the declaration namespace with `Langlands.NYLL`;
- replaced the two upstream imports by the two focused imports above and
  dropped the unused `open scoped Polynomial PowerSeries`;
- prefixed the docstrings with their unit numbers, replaced the module
  documentation, added the modification notice in the Lean header, and wrote
  this paired Markdown.
