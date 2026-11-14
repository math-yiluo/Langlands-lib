# Residue reduction targets for the standard division polynomials (M340.001–003)

This module states, as Prop-valued definitions, the three residue-reduction
assertions of NYLL M340.001–003. It supplies no proofs.

## Common parameters

All three targets live in `Langlands.NYLL.LubinTate`, with independent
universes `u v` and, in source order:

- implicit `{K : Type u} [Field K]` (from the section `variable`);
- implicit `{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K}`;
- implicit `{π : F.valuationSubring}`;
- explicit `(hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))`;
- for the last two targets only, explicit `(n : ℕ)`.

`F.valuationSubring`, `F.residueField` and `F.residueMap` are the published
abbreviations of the shared `LocalField` package (M334.003, .002, .005). The
uniformizer hypothesis is Mathlib's `Valuation.IsUniformizer` for the chosen
valuation `F.toCompleteDVF.valuation : Valuation K F.ValueGroup`, evaluated at
the image of `π` in `K`, with the rank-one discrete structure supplied by the
`CompleteDVF` instance `IsCompleteDiscrete.isRankOneDiscrete`. It says
`v π` is the chosen generator of the value group below one.

The conclusions never mention `hπ`, but it is kept as an explicit binder,
exactly as in the source; consequently each target is a family of
propositions indexed by such a proof. Each definition is preceded by
`set_option linter.unusedVariables false in`, only to silence the unused-binder
warning while keeping the source binder name `hπ`; this option has no effect
on the elaborated type.

Write `q = Nat.card F.residueField`, `f = standardLubinTatePolynomial F π`
(`X ^ q + C π * X`), `f^[n] = standardLubinTatePolynomialIterate F π n`
(the `n`-fold composite of `f` applied to `X`) and
`Qₙ = standardLubinTatePrimitivePolynomial F π n`
(`f^[n] ^ (q - 1) + C π`). All three are polynomials over `F.valuationSubring`,
and `Polynomial.map F.residueMap` reduces their coefficients modulo the
maximal ideal. The subtraction `q - 1` is natural-number subtraction, as in
the source.

## The targets

| Unit | Declaration | Asserts |
| --- | --- | --- |
| M340.001 | `standardLubinTatePolynomial_map_residueStatement hπ` | `(standardLubinTatePolynomial F π).map F.residueMap = Polynomial.X ^ Nat.card F.residueField`, i.e. `f` reduces to `X ^ q`. |
| M340.002 | `standardLubinTatePolynomialIterate_map_residueStatement hπ n` | `(standardLubinTatePolynomialIterate F π n).map F.residueMap = Polynomial.X ^ (Nat.card F.residueField ^ n)`, i.e. `f^[n]` reduces to `X ^ (q ^ n)`. |
| M340.003 | `standardLubinTatePrimitivePolynomial_map_residueStatement hπ n` | `(standardLubinTatePrimitivePolynomial F π n).map F.residueMap = Polynomial.X ^ ((Nat.card F.residueField - 1) * Nat.card F.residueField ^ n)`, i.e. `Qₙ` reduces to `X ^ ((q - 1) * q ^ n)`. |

Mathematically these hold because a uniformizer lies in the maximal ideal, so
`C π * X` reduces to zero; the iterate statement follows by induction on `n`
via `f^[n + 1] = f.comp f^[n]`, and the primitive statement from the iterate
statement and `π ↦ 0`. These remarks describe the source proofs; this module
proves nothing. Separately accepted exact proofs remain required.

## Original source

Naganori Yamaguchi, NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveEisenstein.lean`,
SHA-256 `50d30d87957974e1bf1b9c297ea2b4430cd4a37ac78ab26b38c8e1895414e815`.
The file context (header, imports, `noncomputable section`,
`open scoped Polynomial`, `universe u v`, `namespace LubinTate`,
`open LocalFieldTheory.DiscreteValuationField`, `variable {K : Type u} [Field K]`)
is at lines 1–42.

| Unit | Source theorem | Statement lines | Proof lines |
| --- | --- | --- | --- |
| M340.001 | `LubinTate.standardLubinTatePolynomial_map_residue` | 44–50 (docstring 44–45, declaration from 46) | 50–52 |
| M340.002 | `LubinTate.standardLubinTatePolynomialIterate_map_residue` | 54–60 (docstring 54–55, declaration from 56) | 60–69 |
| M340.003 | `LubinTate.standardLubinTatePrimitivePolynomial_map_residue` | 71–79 (docstring 71–72, declaration from 73) | 79–83 |

Registered sources: `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), under
`n-yamaguchi-0729--ClassFieldTheory/source/`, and attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The project errata lookup has no entry for this source.

## Modifications

Made by Worker 419, 2026-11-14:

- Namespace `LubinTate` becomes `Langlands.NYLL.LubinTate`; the opened
  namespace `LocalFieldTheory.DiscreteValuationField` resolves to the
  published `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`.
- Each `theorem` becomes a `def` returning `Prop`, named by appending
  `Statement`; the binders and the conclusion are copied unchanged, and the
  proofs (which used the source lemma
  `SameUniformizer.residueMap_uniformizer_eq_zero`, M336.001, and
  `standardLubinTatePolynomialIterate_succ`, M339.010) are omitted.
- `set_option linter.unusedVariables false in` is added before each
  definition, as explained above.
- The source imports (`Nyll.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial`
  and `Mathlib.RingTheory.Polynomial.Eisenstein.Basic`) are replaced by the
  single published import
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions`
  (M339.014, `standardLubinTatePrimitivePolynomial`). It transitively
  provides `standardLubinTatePolynomial` (M339.001, module
  `…FiniteLevel.DivisionPolynomial.Definitions`),
  `standardLubinTatePolynomialIterate` (M339.008, module
  `…FiniteLevel.DivisionPolynomial.Iterate.Definitions`), the `LocalField`
  package, Mathlib's `Polynomial.map` and `Valuation.IsUniformizer`. The
  Eisenstein import is needed only by M340.004, which is not included. The
  polynomial data are consumed by their published Lean names; nothing is
  redefined here.
- `open scoped Polynomial` is dropped since no `R[X]` notation is used.
- The Eisenstein theorem M340.004 and the remainder of the source file are not
  included.
- The module documentation is replaced.

The original copyright, Apache-2.0 notice and author line are retained in the
Lean header; the license and notice files are `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
