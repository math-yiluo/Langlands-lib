# NYLL M298.028–.029: unconditional compositum norm and order targets

Worker 535, 14 November 2026. Task 6118
(`d6b00e90-7fd3-4bcb-8afc-142249963840`), revision 1.

## Scope

This module supplies the two unconditional proposition targets M298.028 and
M298.029 using the published actual finite abelian subextensions, compositum,
field-inclusion order, norm subgroup, valuation data and class-field axiom.
It supplies no proofs. Every prerequisite was checked in the Library at commit
`320321b3cd4b5100d54cf785192677d59479e65f`; its workspace file matched the
published file.

## Source and attribution

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`.
The file has SHA-256
`0bc99c03d0936ca803d6497174ef17999b76789381f183f525a9f098eac7fd83`.
The source is retained in
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original Apache-2.0 copyright and author header is retained. The Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.

The declaration partition and namespace policy are recorded in
`notes/reuse/nyll-public-port-plan.md`; the M298 rows are in
`notes/reuse/nyll-public-port/m289-m312.md`. That inventory records no patch10
compatibility edit for this source module.

## Source-to-adapted name map

The full original prefix is `ClassFormation.FiniteAbelianSubextension.`;
the full adapted prefix is
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.`.

| Unit | Original theorem suffix | Source statement | Source proof | Adapted definition suffix |
| --- | --- | --- | --- | --- |
| M298.028 | `normSubgroup_compositum` | lines 782–789 | lines 789–798 | `normSubgroup_compositumStatement` |
| M298.029 | `le_iff_normSubgroup_le` | lines 803–809 | lines 809–817 | `le_iff_normSubgroup_leStatement` |

The shared source scaffolding is at lines 739–748, with the universe comment
and `G` parameters at lines 743–744 and `D`, `A` at line 748. The original
docstrings are at lines 777–781 and 800–802.

## Complete statements

Both definitions have this complete common telescope, in the source order
and with the source binder kinds:

```lean
{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
{D : DegreeData G} {A : Rep ℤ G}
(v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
[IsTopologicalGroup G] [CompactSpace G] [T2Space G]
[TotallyDisconnectedSpace G]
(K : FiniteAbstractField G)
(L₁ L₂ : FiniteAbelianSubextension K.field)
```

`IntegralRepGroupType` is the published alias `Type 0`; this follows the
source universe boundary for `Rep ℤ G`. In particular, the targets do not
generalize the universe of `G`. `D`, `A` are implicit, while `v`, `hcf`, `K`,
`L₁`, `L₂` are explicit. The four topology assumptions occur after `hcf`,
exactly as in the source. The valuation and axiom arguments remain parameters
even though neither conclusion mentions their values.

`normSubgroup_compositumStatement v hcf K L₁ L₂` is the proposition

```lean
(L₁.compositum L₂).normSubgroup A =
  L₁.normSubgroup A ⊓ L₂.normSubgroup A
```

Here `compositum` is the actual finite abelian compositum, and `normSubgroup`
is the actual finite norm subgroup in the fixed-coefficient additive ambient
group over `K.field`. The infimum of the two additive subgroups is their
intersection.

`le_iff_normSubgroup_leStatement v hcf K L₁ L₂` is the proposition

```lean
L₁ ≤ L₂ ↔ L₂.normSubgroup A ≤ L₁.normSubgroup A
```

The left order is the published finite-abelian field-inclusion order,
represented by reverse containment of the associated closed Galois subgroups.
The right order is ordinary inclusion of the actual additive norm subgroups.
The declaration is the exact unconditional target: it has no extra
reciprocity-bijectivity, unit-cohomology, or compositum-norm premise.

These definitions state propositions only. In the source proofs, the
class-field axiom supplies the unit-cohomology input, and finite reciprocity
supplies the bijectivity inputs to the previously conditional results. Those
proofs are outside this task and are not included in these definitions.

## Published imports

All module names below have the prefix
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.`.

| Imported module suffix | Used declarations or instances |
| --- | --- |
| `Reciprocity.ClassFieldAxiom.Definitions` | `SatisfiesClassFieldAxiom`; transitive `IntegralRepGroupType`, `DegreeData`, `FiniteAbstractField` |
| `Reciprocity.FiniteAbelianSubextension.Order` | Actual field-inclusion `PartialOrder` |
| `Reciprocity.FiniteAbelianSubextension.Compositum` | Actual `FiniteAbelianSubextension.compositum` |
| `Reciprocity.FiniteAbelianSubextension.NormSubgroup.Definitions` | Actual `FiniteAbelianSubextension.normSubgroup` |
| `Degree.Valuation.ValuationData.Definitions` | `ValuationData` |

The actual finite-abelian foundation is published in
`Reciprocity.FiniteAbelianSubextension.Definitions`. The imported norm-subgroup
definition specializes the published `finiteNormSubgroup`, the actual relative
norm image, using the packaged extension's finite quotient. The imported
compositum uses the intersection of the associated closed Galois subgroups.
The statements reuse these definitions by Lean name.

## Modifications

1. Prefix the source namespace with `Langlands.NYLL`; extract only M298.028
   and M298.029 into this focused module.
2. Replace each source theorem by a `def` with explicit result type `Prop`
   and suffix `Statement`. The body is exactly the source conclusion and
   the source proof is omitted.
3. Spell out the enclosing source section parameters in each declaration
   instead of relying on Lean to select section variables. Every source
   parameter and instance binder, including explicit unused `v`, `hcf`, is
   retained in its original order.
4. Replace the broad source imports
   `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldCandidate`
   and `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main` by
   the focused published imports in the table. Their reduced import closure
   was checked successfully.
5. Omit the unused `open CyclicCohomology KummerTheory` and
   `noncomputable section`: these proposition bodies use neither an opened
   name nor a computational definition. Introduce no new instances or local
   quotient wrappers; the bodies use the packaged operations directly.
6. Replace the module documentation by the extraction and modification
   record, and shorten each declaration docstring to describe its target.
7. Apply `set_option linter.unusedVariables false in` to each declaration
   so that the required unused arguments and instances can remain without
   linter warnings. This does not change the proposition or its telescope.

## Development validation

On 14 November 2026, the Lean service compiled the focused import closure in
approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`: Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
All 46 project prerequisite modules were supplied in dependency order, followed
by this statement module. Both exact declaration inspections succeeded with
`statement_returns_prop = true`, no errors and no warnings.

A private `#print` harness also compiled successfully. Its elaborated output
retains implicit `G`, `D`, `A`, both initial instances, explicit `v`, `hcf`,
the four subsequent topology instances, and explicit `K`, `L₁`, `L₂`, in
the documented order. The acting group and all coefficient and extension types
remain at universe zero; neither declaration has a universe parameter.
The printed bodies are exactly the two displayed conclusions.

These checks establish development compilation, the proposition result types,
and the elaborated telescopes. They do not prove the propositions or replace
independent semantic review and Library integration.
