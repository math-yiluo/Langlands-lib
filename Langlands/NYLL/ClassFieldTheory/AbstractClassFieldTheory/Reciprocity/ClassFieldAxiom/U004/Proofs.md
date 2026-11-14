# The degree-minus-one half of the class field axiom (NYLL M072.004)

This module proves the published proposition
`Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom.tateHMinusOne_cardStatement`
by the theorem
`Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom.tateHMinusOne_card`.
Its sole import is the statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Statements`,
which is left unchanged.

## Target and mathematical meaning

The theorem has the statement telescope, in the source order: implicit
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and
`{A : Rep ℤ G}` (section variables), then explicit
`(hcf : SatisfiesClassFieldAxiom A) (K : FiniteAbstractField G)
(E : FiniteCyclicSubextension K)`. Its type is
`tateHMinusOne_cardStatement hcf K E`, which unfolds to

```lean
Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1
```

Mathematically: if `A` satisfies the class field axiom, then for every finite
abstract field `K` and every finite cyclic subextension `L / K` (bundled as
`E`), the Tate cohomology group `Ĥ⁻¹(G(L/K), A_L)` of the fixed module `A_L`
has order one. (`Nat.card` is `0` on infinite types, so the equation also
forces finiteness.)

## Implemented proof

The proof is the source term proof, unchanged:
`(hcf K E).tateHMinusOne_card`. By definition
(`Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom` in the definitions
module), `hcf K E` is a term of the structure
`ClassFieldAxiomCohomologyData A K E`, and its field `tateHMinusOne_card` has
type `Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1`. The target
`tateHMinusOne_cardStatement hcf K E` unfolds definitionally to exactly this
proposition, so the term checks against the target without any tactic.

The only dependencies are the published definitions
`SatisfiesClassFieldAxiom` and `ClassFieldAxiomCohomologyData` (M072.001 and
M072.002, in `...ClassFieldAxiom.Definitions`, imported through the statement
module) and the target statement. No auxiliary declaration, instance or simp
attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean:79–83`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean#L79-L83)
(partition unit lines 79–86; docstring at lines 77–78), retained locally as
[the pinned snapshot](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean>).

| Original (namespace `ClassFormation.SatisfiesClassFieldAxiom`) | Adapted |
| --- | --- |
| Theorem `tateHMinusOne_card`, lines 79–83 | This theorem, same name under `Langlands.NYLL.` |
| Docstring, lines 77–78 | Unchanged |
| Binders, lines 80–81; section variables, lines 34 and 66 | Unchanged |
| Conclusion, line 82 | `tateHMinusOne_cardStatement hcf K E` (definitionally the source conclusion) |
| Term proof, line 83 | Unchanged |

Other adaptations: the `Langlands.NYLL` namespace prefix; the single statement
import in place of the source import; omission of the source
`noncomputable section`, which a theorem does not need.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 23's dated modification record. The proof body was given in Task 6498 by Worker 5264, who compiled it against the same environment; Worker 23 checked it against the pinned original and the frozen statement module. The unchanged inherited
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
