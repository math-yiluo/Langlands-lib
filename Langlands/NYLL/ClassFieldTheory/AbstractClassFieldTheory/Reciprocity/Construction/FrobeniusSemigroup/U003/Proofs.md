# Frobenius multiplication on representatives (NYLL M015.003)

Worker 754, 16 November 2026. This module proves the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusMul_coeStatement`
by the theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusMul_coe`.
Its sole import is the statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup.Statements`,
which is left unchanged.

## Target and mathematical meaning

The theorem has the statement telescope, in the source order: the section
variables `{G : Type*} [Group G] [TopologicalSpace G]`, then explicit
`(D : DegreeData G) (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
(hLK : L.toSubgroup ≤ K.field.toSubgroup)`, the instance binder
`[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]`, and
explicit `(σ τ : D.FrobeniusElements K L hLK)`. Its type is
`D.frobeniusMul_coeStatement K L hLK σ τ`, which unfolds to

```lean
(σ * τ).1 = σ.1 * τ.1
```

Mathematically: `D.FrobeniusElements K L hLK` is the subtype of the
inertia quotient `G_K / I_L` (here `K.field.toSubgroup ⧸
D.extensionInertiaWithin K.field L hLK`) of classes whose extension
normalized degree is a positive power of `Multiplicative.ofAdd (1 : ZHat)`;
the product of two such Frobenius elements in the Frobenius semigroup is
represented by the product of their classes in that quotient group.

## Implemented proof

The proof is the source term proof, unchanged: `rfl`. The multiplication on
`D.FrobeniusElements K L hLK` is the published instance
`frobeniusElementsMul` (M015.002), whose operation is the published
definition `frobeniusMul` (M015.001). That definition is built by
`refine ⟨σ.1 * τ.1, m + n, _, ?_⟩`, so the first component of `σ * τ` is
definitionally `σ.1 * τ.1`; the proof-valued second component does not
affect the value. Hence both sides of the target are definitionally equal and
`rfl` checks against the target statement without unfolding any lemma.

The only dependencies are the published definitions `FrobeniusElements`,
`frobeniusMul` and the instance `frobeniusElementsMul` (imported through the
statement module) and the target statement. No auxiliary declaration,
instance or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean:58–65`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean#L58-L65)
(partition unit lines 58–67, docstring and attribute at lines 56–57), retained
locally as
[the pinned snapshot](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean>).

| Original (namespace `ClassFormation.DegreeData`) | Adapted |
| --- | --- |
| Theorem `frobeniusMul_coe`, lines 58–65 | This theorem, same name under `Langlands.NYLL.` |
| Docstring, line 56 | Unchanged |
| `@[simp]` attribute, line 57 | Omitted (proof modules add no simp attributes) |
| Binders, lines 59–63; section variable, line 26 | Unchanged, except the instance binder below |
| `[hLnormal : (CyclicCohomology.extensionSubgroup (G := G) K.field L hLK).Normal]`, lines 61–62 | `[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]`, the exact Mathlib body of `extensionSubgroup`, as in the statement |
| Conclusion, line 64 | `D.frobeniusMul_coeStatement K L hLK σ τ` (definitionally the source conclusion) |
| Term proof `rfl`, line 65 | Unchanged |

Other adaptations: the `Langlands.NYLL` namespace prefix; the single statement
import in place of the source import; omission of the then unused
`open CyclicCohomology` and of the source `noncomputable section`, which a
theorem does not need.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 754's dated modification record. The unchanged
inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The whole source file has SHA-256
`d11fc29514c9a12171d2a10287d09d10aa13b765641c57893c102aa7a6a70a06`, recomputed by
Worker 754 on 16 November 2026 UTC. The
[port partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m015)
lists this unit as M015.003.

This support proof discharges no host class-formation, cup, transfer, Tate or
reciprocity target.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), where the module
compiles with no errors or warnings and the theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. Compilation is not acceptance:
publication under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
