# The derivative of `X ^ 2 - X` at a quotient idempotent is a unit (NYLL M104.003)

This module proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotentStatement`
by the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent`.
Its sole import is the statement module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements`,
which is left unchanged.

## Target and mathematical meaning

The theorem keeps the statement's binders in their order: implicit
`R : Type*` (universe polymorphic) with `[CommRing R]`, implicit
`I : Ideal R`, explicit `a0 : R` and
`ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)`. Its type is
`idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotentStatement a0 ha0`,
which unfolds to
`IsUnit (Ideal.Quotient.mk I ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0))`.

Mathematically: if the class `e` of `a0` in `R ⧸ I` is idempotent, then the
class of the derivative `2X - 1` evaluated at `a0`, namely `2e - 1`, is a unit
of `R ⧸ I`; it is its own inverse because
`(2e - 1) ^ 2 = 1 + 4 (e ^ 2 - e) = 1`.

## Implemented proof

After `unfold idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotentStatement`,
the rest is the unchanged source tactic proof. `isUnit_iff_exists` reduces the
goal to exhibiting a two-sided inverse; the proof offers the element itself.
For each of the two products, `simp only` with `pow_two`,
`Polynomial.derivative_mul`, `Polynomial.derivative_X`, the evaluation lemmas
and `map_sub`, `map_add`, `map_one` rewrites the class of the derivative to
`mk a0 + mk a0 - 1`. A `calc` then rewrites
`(mk a0 + mk a0 - 1) * (mk a0 + mk a0 - 1)` by `ring` as
`1 + (4 * (mk a0 * mk a0) - 4 * mk a0)`, substitutes `mk a0 * mk a0 = mk a0`
(`ha0.eq`) and closes `1 + (4 * mk a0 - 4 * mk a0) = 1` by `ring`. The two
bullets are identical, as in the source.

The proof uses only Mathlib (`Mathlib.Algebra.Group.Units.Defs`,
`Mathlib.Algebra.Polynomial.Derivative`, the quotient-ring homomorphism and
`ring`, available through the statement module's imports). No auxiliary
declaration, instance or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi, [`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean:47–83`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean#L47-L83)
(partition unit lines 47–89; docstring at lines 45–46).

| Original (namespace `ValuationTheory.DiscreteValuationField`) | Adapted |
| --- | --- |
| Theorem `idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent`, lines 47–83 | This theorem, same name under `Langlands.NYLL.` |
| Conclusion `IsUnit (Ideal.Quotient.mk I ((X ^ 2 - X).derivative.eval a0))` (lines 50–52) | `idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotentStatement a0 ha0` |
| Tactic proof, lines 53–83 | Identical, preceded by one `unfold` |

Adaptations: the namespace gains the `Langlands.NYLL` prefix; the source imports
are replaced by the single statement import; the conclusion is written as the
published statement applied to the source binders and unfolded first; the
`noncomputable section` and the unused `universe u v` are omitted.

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
