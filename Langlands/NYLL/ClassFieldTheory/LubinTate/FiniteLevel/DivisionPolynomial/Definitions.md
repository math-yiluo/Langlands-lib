# The standard Lubin–Tate polynomial (M339.001)

This module extracts exactly source unit M339.001, the definition at line 51
(docstring and body lines 49–55) of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean#L49-L55)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The source file's
SHA-256 is
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
Its header, imports, module documentation, universe, namespace and variable
context (lines 1–47) and the following declarations were read directly.

The original is in the registered source
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The project has no errata note for either source.

## Declaration

`Langlands.NYLL.LubinTate.standardLubinTatePolynomial` has independent
universe parameters `u v`, implicit `{K : Type u} [Field K]`, and explicit
arguments `(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)`
and `(π : F.valuationSubring)`. Its type is
`Polynomial F.valuationSubring`, and its body is

```lean
Polynomial.X ^ Nat.card F.residueField + Polynomial.C π * Polynomial.X
```

that is, the polynomial `X ^ q + π * X` over the valuation ring, where
`q = Nat.card F.residueField` is the natural cardinality of the residue field
of the chosen local-field package. The coefficient `π` is an arbitrary
element of the valuation ring: no uniformizer hypothesis is assumed, as in
the source. The definition is `noncomputable`, as in the source.

The local-field package `F`, its valuation subring and its residue field are
the published Library declarations
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`,
`.LocalField.valuationSubring` and `.LocalField.residueField`, from
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`.
No local-field, valuation, residue or uniformizer data are duplicated or
chosen here. The polynomial ring, `Polynomial.X`, `Polynomial.C` and
`Nat.card` are Mathlib's.

## Exact source correspondence

| Source unit and declaration | Adapted declaration | Type and body |
| --- | --- | --- |
| M339.001, `LubinTate.standardLubinTatePolynomial`, line 51 (lines 49–55 with docstring) | `Langlands.NYLL.LubinTate.standardLubinTatePolynomial` | `(F : LocalField.{u, v} K) (π : F.valuationSubring) : Polynomial F.valuationSubring := Polynomial.X ^ Nat.card F.residueField + Polynomial.C π * Polynomial.X`; unchanged. |

The source opens `LocalFieldTheory.DiscreteValuationField` inside namespace
`LubinTate`; the adapted file opens the same relative name inside
`Langlands.NYLL.LubinTate`, which resolves to the published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`. The variable line
`{K : Type u} [Field K]`, the universes `u v`, the docstring, the
`noncomputable section` and `open scoped Polynomial` are retained.

## Namespace, imports and API

- Namespace: `LubinTate` becomes `Langlands.NYLL.LubinTate`.
- Imports: the source imports
  `Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardSeries` and
  `Mathlib.Algebra.Polynomial.Monic`. This definition uses neither the
  standard series nor monicity, so the imports are replaced by:
  - `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`
    (the published local-field package);
  - `Mathlib.Algebra.Polynomial.Basic` (polynomials, `X`, `C`);
  - `Mathlib.SetTheory.Cardinal.Finite` (`Nat.card`).
- The source's `open scoped PowerSeries` is dropped, since no power series
  appears here.
- API: one new declaration, `Langlands.NYLL.LubinTate.standardLubinTatePolynomial`.
  No existing Library declaration is changed.

## Scope

Only M339.001 is extracted. The source's formula, evaluation and power-series
correspondences (M339.002–005), its iterate and factor definitions and their
lemmas (M339.008 onward) are excluded. The degree and monicity targets
M339.006–007 are stated in the sibling module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.DegreeStatements`.
No theorem is proved and no instance is added.

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

- extracted M339.001 and its docstring into this focused module, omitting
  all other source declarations;
- prefixed the declaration namespace with `Langlands.NYLL`;
- replaced the two upstream imports by the three focused imports above and
  dropped the unused `open scoped PowerSeries`;
- replaced the module documentation, added the modification notice in the
  Lean header, and wrote this paired Markdown.

The declaration's parameters, universes, type and body are unchanged apart
from the namespace.
