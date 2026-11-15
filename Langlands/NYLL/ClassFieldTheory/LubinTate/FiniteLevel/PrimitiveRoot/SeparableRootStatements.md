# Primitive polynomial separability and root-existence targets (M341.009–011)

This module states three Prop-valued targets of NYLL M341 about the
field-valued primitive Lubin–Tate polynomial
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomialOverField F π n`,
that is, the level-`n + 1` primitive division polynomial
`f^[n] ^ (q - 1) + π` (with `f = X ^ q + π * X` and `q` the cardinality of
the residue field) mapped from the valuation subring of `F` to `K`.

All three targets share the source parameters, in source order:
independent universes `u v`; implicit `{K : Type u} [Field K]`; implicit
`{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K}`
and `{π : F.valuationSubring}`; an explicit hypothesis
`(_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))` that `π` is a
uniformizer of the chosen valuation; and an explicit level `(n : ℕ)`.

| Source | Lean target | Asserts |
| --- | --- | --- |
| M341.009, line 148 | `Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomialOverField_derivative_ne_zeroStatement` | `(standardLubinTatePrimitivePolynomialOverField F π n).derivative ≠ 0` |
| M341.010, line 191 | `Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomialOverField_separableStatement` | `(standardLubinTatePrimitivePolynomialOverField F π n).Separable` |
| M341.011, line 200 | `Langlands.NYLL.LubinTate.exists_standardLubinTatePrimitivePolynomialOverField_rootStatement` | `∃ x : SeparableClosure K, ((standardLubinTatePrimitivePolynomialOverField F π n).map (algebraMap K (SeparableClosure K))).IsRoot x` |

`Polynomial.Separable` is Mathlib's separability (coprimality with the
derivative). `SeparableClosure K` is Mathlib's separable closure of `K`
inside its algebraic closure (`Mathlib.FieldTheory.IsSepClosed`), the same
object the source uses; the third target asserts only that some root
exists there. The uniformizer hypothesis does not occur in any of the
three conclusions; it is retained because the source theorems take it and
their proofs use it (nonvanishing of `π ^ n`, and Eisenstein
irreducibility).

## Scope

The pair states targets only and proves nothing. It asserts neither the
nonvanishing of the derivative, nor separability, nor the existence of a
root. It contains no chosen root (the source's
`chosenStandardLubinTatePrimitiveRoot`, line 222, and everything after
line 205 are excluded), no irreducibility target (M341.007, owned by
Task 6147) and no helper lemmas: the source's derivative-at-zero lemmas
(lines 44–69), the polynomial-map formula M341.004 (line 80) and the
residue-cardinality lemma (line 123) are excluded.

## Source and modifications

Original source: Naganori Yamaguchi, NYLL ClassFieldTheory,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`, file SHA-256
`b9d4862f4873c982618ff0f591c73b251f7a6f6f3d4fc6e93134b6d4ecb732b4`.
Signatures and conclusions: M341.009 at lines 147–151, M341.010 at
lines 190–194, M341.011 at lines 199–205; context (`noncomputable section`,
`open scoped Polynomial`, `universe u v`, `namespace LubinTate`,
`open LocalFieldTheory.DiscreteValuationField`,
`variable {K : Type u} [Field K]`) at lines 32–42. Registered sources
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Worker 423 made the following modifications:

- extracted only the three statements; each source `theorem` became a
  Prop-valued `def` whose name is the source name with the suffix
  `Statement`, and all proofs were omitted;
- prefixed the namespace with `Langlands.NYLL`
  (`LubinTate` → `Langlands.NYLL.LubinTate`); the opened namespace
  `LocalFieldTheory.DiscreteValuationField` resolves to the published
  `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`;
- renamed the unused proof binder `hπ` to `_hπ`, which silences the
  unused-variable linter without changing the type, binder order or
  explicitness;
- replaced the source imports (the whole `PrimitiveEisenstein` module,
  `Mathlib.RingTheory.Polynomial.GaussLemma` and
  `Mathlib.SetTheory.Cardinal.Finite`) by the published definition module
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.FieldPolynomial`
  (which provides `standardLubinTatePrimitivePolynomialOverField`) and
  `Mathlib.FieldTheory.IsSepClosed` (retained from the source, for
  `SeparableClosure`);
- replaced the module documentation and added the modification notice
  to the header.

No hypotheses, instances or universe identifications are added. The
original copyright, Apache-2.0 and author lines are retained;
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are
unchanged.
