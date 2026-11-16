# The idempotent polynomial is monic (NYLL M104.001)

This module proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.idempotentPolynomial_monicStatement`
by the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.idempotentPolynomial_monic`.
Its sole import is the statement module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements`,
which is left unchanged.

## Target and mathematical meaning

The theorem keeps the statement's binders: implicit `R : Type*` (universe
polymorphic) with `[CommRing R] [Nontrivial R]`. Its type is
`idempotentPolynomial_monicStatement (R := R)`, which unfolds to
`(Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic`.

Mathematically: in every nontrivial commutative ring `R`, the polynomial
`X ^ 2 - X ∈ R[X]` has leading coefficient `1`.

## Implemented proof

After `unfold idempotentPolynomial_monicStatement`, the rest is the unchanged
source tactic proof. Mathlib's `Polynomial.monic_X_pow_sub` says that
`X ^ n - p` is monic whenever `degree p < n`. With `p := X` and `n := 2`, the
side condition `degree X < 2` is rewritten by `Polynomial.degree_X` (which uses
`Nontrivial R`) to `1 < 2` in `WithBot ℕ`, closed by `norm_num`.

The proof uses only Mathlib (`Mathlib.Algebra.Polynomial.Monic` and
`Mathlib.Algebra.Polynomial.Degree.Defs`, available through the
statement module's imports). No auxiliary declaration, instance or simp
attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi, [`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean:27–32`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean#L27-L32)
(partition unit lines 27–34; docstring at lines 25–26).

| Original (namespace `ValuationTheory.DiscreteValuationField`) | Adapted |
| --- | --- |
| Theorem `idempotentPolynomial_monic`, lines 27–32 | This theorem, same name under `Langlands.NYLL.` |
| Conclusion `(Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic` (line 29) | `idempotentPolynomial_monicStatement (R := R)` |
| Tactic proof, lines 30–32 | Identical, preceded by one `unfold` |

Adaptations: the namespace gains the `Langlands.NYLL` prefix; the source imports
are replaced by the single statement import; the conclusion is written as the
published statement and unfolded first; the `noncomputable section` and the
unused `universe u v` are omitted.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 740's dated modification record. Worker 740
extracted this proof directly from the pinned original and the published
statement module; there are no project coauthors. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The whole source file has SHA-256
`cce4a6ecfed6076732a5041ad23935a638de6eb5c3c35287d289c8b1717e0cf2`, recomputed by
Worker 740 on 16 November 2026 UTC. The
[port partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m104)
lists this unit in module M104 (no patch10 edit applies).

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), where the module
compiles with no errors or warnings and the theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. Compilation is not acceptance:
publication under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
