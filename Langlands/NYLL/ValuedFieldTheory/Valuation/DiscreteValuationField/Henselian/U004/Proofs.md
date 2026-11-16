# Idempotents lift along a surjection with Henselian kernel (NYLL M104.004)

This module proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.exists_idempotent_lift_of_surjective_henselianRing_kerStatement`
by the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.exists_idempotent_lift_of_surjective_henselianRing_ker`.
Its sole import is the statement module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements`,
which is left unchanged.

## Target and mathematical meaning

The theorem keeps the statement's binders in their order: implicit
`R S : Type*` (independent universes) with `[CommRing R] [CommRing S]`,
explicit `f : R →+* S` and `hf : Function.Surjective f`, the instance
`[HenselianRing R (RingHom.ker f)]`, explicit `e : S` and
`he : IsIdempotentElem e`. Its type is
`exists_idempotent_lift_of_surjective_henselianRing_kerStatement f hf e he`,
which unfolds to `∃ e' : R, IsIdempotentElem e' ∧ f e' = e`.

Mathematically: let `f : R → S` be a surjective ring homomorphism such that
`(R, ker f)` is a Henselian pair (Mathlib's `HenselianRing`: `ker f` lies in
the Jacobson radical and every monic polynomial with a simple root modulo
`ker f` has a root lifting it). Then every idempotent `e` of `S` is `f e'`
for an idempotent `e'` of `R`.

## Implemented proof

After `unfold exists_idempotent_lift_of_surjective_henselianRing_kerStatement`
the proof follows the source tactic proof, case by case on
`subsingleton_or_nontrivial R`.

- If `R` is a subsingleton, so is `S`, since every pair of elements of `S`
  is the image of a pair of (equal) elements of `R` by surjectivity. Then
  `e' := 0` works, both conditions being equalities in subsingletons.
- If `R` is nontrivial, choose `a0` with `f a0 = e` and put
  `p := X ^ 2 - X`. The class of `a0` modulo `ker f` is idempotent, since
  `f (a0 * a0 - a0) = e * e - e = 0` (`Ideal.Quotient.eq`, `RingHom.mem_ker`,
  `he.eq`). Three local facts follow:
  `p` is monic; `p.eval a0 ∈ ker f`; and the class of `p.derivative.eval a0`
  modulo `ker f` is a unit. Then `HenselianRing.is_henselian` supplies a root
  `a` of `p` with `a - a0 ∈ ker f`. Being a root of `X ^ 2 - X` means
  `a * a = a`, and `f (a - a0) = 0` gives `f a = f a0 = e`.

The three local facts are exactly the statements of M104.001, M104.002 and
M104.003 (for the ideal `RingHom.ker f`), which the source proof cites as
theorems. Those theorems were not yet in the Library when this proof was
written, so each is proved in place by a local `have` whose tactic script is
the corresponding source proof (lines 30–32, 39–43 and 53–83), with
`I := RingHom.ker f` and the hypothesis `ha0_quotient`. Inside the second and
third `have` a `dsimp [p]` first unfolds the local abbreviation `p`, which
replaces the source's `simpa [p] using ...` adaptation of the cited
theorem's conclusion. No declaration named after M104.001–.003 is added, so
the published proofs of those units remain the only ones under their names.

The proof uses only Mathlib (`Mathlib.RingTheory.Henselian`, through the
statement module's imports, and basic polynomial, quotient and ring-hom
lemmas). No auxiliary declaration, instance or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi, [`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean:90–136`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean#L90-L136)
(partition unit lines 90–138; docstring at lines 85–89).

| Original (namespace `ValuationTheory.DiscreteValuationField`) | Adapted |
| --- | --- |
| Theorem `exists_idempotent_lift_of_surjective_henselianRing_ker`, lines 90–136 | This theorem, same name under `Langlands.NYLL.` |
| Conclusion `∃ e' : R, IsIdempotentElem e' ∧ f e' = e` (line 95) | `exists_idempotent_lift_of_surjective_henselianRing_kerStatement f hf e he` |
| Case split, subsingleton case and nontrivial set-up (`a0`, `p`), lines 96–108 | Identical |
| `hpmonic` via `idempotentPolynomial_monic`, lines 109–111 | Same `have`, `dsimp [p]` kept, then the source proof of M104.001 (lines 30–32) |
| `ha0_quotient`, lines 112–118 | Identical |
| `hroot` via `idempotentPolynomial_eval_mem_of_quotient_idempotent`, lines 119–122 | Same `have`, proved by `dsimp [p]` and the source proof of M104.002 (lines 39–43) for `RingHom.ker f` |
| `hsimple` via `idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent`, lines 123–128 | Same `have`, proved by `dsimp [p]` and the source proof of M104.003 (lines 53–83) for `RingHom.ker f` |
| Hensel step and conclusion, lines 129–136 | Identical |

Adaptations: the namespace gains the `Langlands.NYLL` prefix; the source imports
are replaced by the single statement import; the conclusion is written as the
published statement applied to the source binders and unfolded first; the
three cited theorems are replaced by their inlined source proofs as described
above; the `noncomputable section` and the unused `universe u v` are omitted.

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
