# Vanishing of `Ĥ⁻¹` under the class field axiom (NYLL M072.005)

This module proves the published proposition
`Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom.tateHMinusOne_isZeroStatement`
by the theorem
`Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom.tateHMinusOne_isZero`.
Its sole import is the statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Statements`,
which is left unchanged.

## Target and mathematical meaning

The theorem has the statement telescope, in the source order: implicit
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and
`{A : Rep ℤ G}` (section variables), then explicit
`(hcf : SatisfiesClassFieldAxiom A) (K : FiniteAbstractField G)
(E : FiniteCyclicSubextension K)`. Its type is
`tateHMinusOne_isZeroStatement hcf K E`, which unfolds to

```lean
CategoryTheory.Limits.IsZero (tateCohomology (E.fixedRepresentation A) (-1))
```

Mathematically: if `A` satisfies the class field axiom, then for every finite
abstract field `K` and every finite cyclic subextension `L / K` (bundled as
`E`), the `ℤ`-module `Ĥ⁻¹(G(L/K), A_L)` is a zero object of `ModuleCat ℤ`,
not merely a group of order one.

## Implemented proof

The tactic proof is the source proof with two changes, both recorded in the
Lean modification header:

1. `change Limits.IsZero (tateCohomology (E.fixedRepresentation A) (-1))`
   first replaces the target `tateHMinusOne_isZeroStatement hcf K E` by its
   definitional unfolding, the source conclusion.
2. The source line `simpa [H] using hcf.tateHMinusOne_card K E` used the
   M072.004 theorem `SatisfiesClassFieldAxiom.tateHMinusOne_card`, which is not
   yet in the Library. The task allows proving such a prerequisite locally
   instead of importing it. The step is therefore the term
   `(hcf K E).tateHMinusOne_card`, which is the source proof of M072.004
   (line 83), inlined. It gives `hcard : Nat.card H = 1`: the field of
   `ClassFieldAxiomCohomologyData A K E` has type
   `Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1`, which agrees
   with `Nat.card H = 1` after unfolding the `let`-bound `H`. No `simpa` is
   needed. The proof adds no declaration, so no second copy of the M072.004
   theorem is published under its adapted name. The public M072.004 theorem is
   staged separately in `ClassFieldAxiom/U004/Proofs.lean`.

The remaining steps are unchanged from the source:

* `H` abbreviates `tateCohomology (E.fixedRepresentation A) (-1)`, an object
  of `ModuleCat ℤ`;
* `(hcf K E).finiteTateHMinusOne` supplies the instance `Finite H`;
* Mathlib's `Nat.card_eq_one_iff_unique` turns `hcard` into
  `Subsingleton H ∧ Nonempty H`, and its first component is installed as an
  instance;
* Mathlib's `ModuleCat.isZero_of_subsingleton H` concludes that `H` is a zero
  object.

Dependencies: the published definitions `SatisfiesClassFieldAxiom` and
`ClassFieldAxiomCohomologyData` (M072.001 and M072.002, imported through the
statement module), the target statement, and the Mathlib lemmas
`Nat.card_eq_one_iff_unique` and `ModuleCat.isZero_of_subsingleton`, both
available through the statement module's imports. No auxiliary declaration,
instance or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean:87–96`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean#L87-L96)
(partition unit lines 87–96; docstring at lines 85–86), retained locally as
[the pinned snapshot](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean>).

| Original (namespace `ClassFormation.SatisfiesClassFieldAxiom`) | Adapted |
| --- | --- |
| Theorem `tateHMinusOne_isZero`, lines 87–96 | This theorem, same name under `Langlands.NYLL.` |
| Docstring, lines 85–86 | Unchanged |
| Binders, lines 88–89; section variables, lines 34 and 66 | Unchanged |
| Conclusion, line 90 | `tateHMinusOne_isZeroStatement hcf K E` (definitionally the source conclusion) |
| Tactic proof, lines 91–96 | A leading `change` to the source conclusion; lines 91–92 and 95–96 unchanged; lines 93–94 become `have hcard : Nat.card H = 1 := (hcf K E).tateHMinusOne_card` |
| Theorem `tateHMinusOne_card` (M072.004), line 83, used at line 94 | Its proof term inlined at that step; not imported |

Other adaptations: the `Langlands.NYLL` namespace prefix; the single statement
import in place of the source import; omission of the source
`noncomputable section`, which a theorem does not need.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 23's dated modification record. The leading `change` and the replacement of the `simpa` step by a term were proposed in Task 6498 by Worker 5264, who compiled that version importing the M072.004 proof module; Worker 23 replaced the import by the inlined M072.004 proof term and checked the result against the pinned original and the frozen statement module. The unchanged inherited
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
`5251ee8dafd55cbbf1dc7258b7a0a577b2a2b3c1d9a4f020f4afce8013211814`, recomputed by
Worker 23 on 14 November 2026 UTC. The
[port partition](../../../../../../../notes/reuse/nyll-public-port/m049-m072.md#m072)
lists this unit in module M072.

This support proof discharges no host class-formation, cup, transfer, Tate or
reciprocity target.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), where the module
compiles with no errors or warnings and the theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. Compilation is not acceptance:
publication under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
