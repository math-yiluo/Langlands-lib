# Eisenstein and irreducibility targets for the standard primitive polynomials (M340.004, M340.006)

This module states two Prop-valued targets about the standard Lubin–Tate
primitive quotient polynomial

`Qₙ(X) = standardLubinTatePrimitivePolynomial F π n
       = (f^[n](X)) ^ (q - 1) + C π`,  where `f(X) = X ^ q + π X`
and `q = Nat.card F.residueField`.

Here `F` is the shared FM local-field package
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
and `Qₙ` is a polynomial over `F.valuationSubring`.

## Declarations

Both declarations live in namespace `Langlands.NYLL.LubinTate`, with universes
`u v` and the same telescope:

- implicit `{K : Type u} [Field K]` (section variables);
- implicit `{F : LocalField.{u, v} K}` and `{π : F.valuationSubring}`;
- explicit `(hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))`;
- explicit `(n : ℕ)`.

| Source unit | Lean name | Proposition |
| --- | --- | --- |
| M340.004 | `standardLubinTatePrimitivePolynomial_isEisensteinAtStatement` | `(standardLubinTatePrimitivePolynomial F π n).IsEisensteinAt F.maximalIdeal` |
| M340.006 | `standardLubinTatePrimitivePolynomial_irreducibleStatement` | `Irreducible (standardLubinTatePrimitivePolynomial F π n)` |

`Polynomial.IsEisensteinAt` is Mathlib's structure requiring that the
leading coefficient is not in the ideal, every lower coefficient is in the
ideal, and the constant coefficient is not in the square of the ideal.
`F.maximalIdeal` is the FM abbreviation for the canonical maximal ideal of
the local ring `F.valuationSubring`. `Irreducible` is Mathlib's monoid
irreducibility in `Polynomial F.valuationSubring`, so the second target is
irreducibility over the valuation ring, not over `K`.

The uniformizer hypothesis states that the valuation of `π`, viewed in `K`,
is the generator of the chosen rank-one discrete value group. It is retained
as an explicit argument of both targets, as in the source, although neither
proposition mentions it. It is needed by the later proofs: for example, with
`π = 0` the constant coefficient of `Qₙ` is `0`, so the Eisenstein
proposition fails.

## Scope

This pair states the two targets and proves nothing. It asserts neither
Eisensteinness nor irreducibility, and it does not state the residue
reductions M340.001–.003 (owned by Task 6143) or the primitivity assertion
M340.005. Proofs of these targets are separate later units.

## Dependencies

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions`
  supplies `Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial`
  (M339.014) and, through its imports, the shared FM `LocalField` package
  with its `valuationSubring`, `maximalIdeal` and `residueField`
  abbreviations and the `toCompleteDVF` projection. The chosen valuation
  `F.toCompleteDVF.valuation` and Mathlib's `Valuation.IsUniformizer`
  come from the published `CompleteDVF` definitions in that import chain.
- `Mathlib.RingTheory.Polynomial.Eisenstein.Basic` supplies
  `Polynomial.IsEisensteinAt`; `Irreducible` is Mathlib's.

No other Library or external declaration is used.

## Source and modifications

Original source: Naganori Yamaguchi, NYLL ClassFieldTheory,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveEisenstein.lean`,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`, file SHA-256
`50d30d87957974e1bf1b9c297ea2b4430cd4a37ac78ab26b38c8e1895414e815`.

- M340.004: `LubinTate.standardLubinTatePrimitivePolynomial_isEisensteinAt`,
  statement at lines 87–91 (proof lines 92–116);
- M340.006: `LubinTate.standardLubinTatePrimitivePolynomial_irreducible`,
  statement at lines 126–129 (proof lines 130–137);
- context: header lines 1–5, imports lines 7–8, `noncomputable section`,
  `open scoped Polynomial`, `universe u v`, `namespace LubinTate`,
  `open LocalFieldTheory.DiscreteValuationField` and
  `variable {K : Type u} [Field K]` at lines 32–42.

Registered sources: `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Modifications by Worker 420:

1. Extraction: only the two statements are kept. The source proofs, the
   residue reductions M340.001–.003 and the primitivity theorem M340.005
   are omitted.
2. Namespace: `LubinTate` becomes `Langlands.NYLL.LubinTate`. The opened
   namespace `LocalFieldTheory.DiscreteValuationField` is written the same
   way and resolves to the published
   `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`.
3. Statement form: each `theorem` becomes a `def … : Prop` whose body is
   the source conclusion verbatim; the name gains the suffix `Statement`.
4. Linter option: the uniformizer binder keeps its source name `hπ`, type,
   explicitness and position. Because the Prop bodies do not use it, each
   definition is preceded by `set_option linter.unusedVariables false in`,
   which affects only that declaration's linting.
5. Imports: the source imports the whole NYLL division-polynomial module
   and Mathlib's Eisenstein basics. This module imports only the published
   primitive-polynomial definition module and
   `Mathlib.RingTheory.Polynomial.Eisenstein.Basic`.
6. Documentation: the module documentation is rewritten for the extracted
   targets; the two declaration docstrings are the source docstrings.

No hypothesis, instance, universe or parameter is added, removed or
reordered, and no definition is duplicated. The original copyright, Apache-2.0
and author lines are retained in the Lean header with a dated modification
notice. `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are
byte-identical to the pinned source's files and are not modified; the source
NOTICE has no entry specific to this file.
