# Extension restriction on quotient representatives

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.extensionRestriction_mk`.
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.extensionRestriction_mkStatement`
applied to the theorem's parameters. This is the proof phase of M012.008 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m012).

## Target and binders

The theorem keeps the section variables and the binders of the target in
the same order:

| Binders | Kind | Meaning |
| --- | --- | --- |
| `G : Type u` | implicit (section variable) | The ambient group |
| `[Group G]`, `[TopologicalSpace G]` | instance-implicit (section variables) | Its group structure and topology |
| `D : DegreeData G` | explicit | The published degree data |
| `K L : ClosedSubgroup G` | explicit | The base field `K` and the extension `L`, as closed subgroups |
| `hLK : L.toSubgroup ≤ K.toSubgroup` | explicit | Containment `G_L ≤ G_K` |
| `[hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]` | instance-implicit | Normality of `G_L` in `G_K` (the extension is Galois) |
| `k : K.toSubgroup` | explicit | An element of `G_K` |

The statement is

```lean
D.extensionRestriction K L hLK (QuotientGroup.mk k) = QuotientGroup.mk k
```

The left `QuotientGroup.mk k` is the class of `k` modulo the relative
inertia `D.extensionInertiaWithin K L hLK`, that is
`G(\widetilde L|K)`. The right `QuotientGroup.mk k` is the class of `k`
modulo `L.toSubgroup.subgroupOf K.toSubgroup`, that is `G(L|K)`. So the
restriction `G(\widetilde L|K) → G(L|K)` sends the class of `k` to the class
of `k`. The theorem adds no hypothesis to the target.

## Implemented proof

The proof is the term `rfl`, as in the source. In the imported published
`FrobeniusLift.Definitions` module, `extensionRestriction` is defined as

```lean
QuotientGroup.map (D.extensionInertiaWithin K L hLK)
  (L.toSubgroup.subgroupOf K.toSubgroup) (MonoidHom.id K.toSubgroup) inf_le_left
```

`QuotientGroup.map N M f h` is `QuotientGroup.lift N ((mk' M).comp f) _`,
and `QuotientGroup.lift` on a class `mk k` reduces by definition to the
lifted homomorphism at `k`. That value is `mk' M (MonoidHom.id _ k)`, which
is `QuotientGroup.mk k`. Lean's kernel checks this definitional unfolding,
so `rfl` proves the closed target. The statement definition
`extensionRestriction_mkStatement` unfolds by definition to this equality,
so the theorem can state the target directly.

A development `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) built the module with Lake with
no diagnostics. The theorem has level parameter `u` and uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`, which come from the imported
definitions and Mathlib. This check is not independent acceptance.

## Imports

The sole import is the published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Statements`
module, which imports `FrobeniusLift.Definitions` (M012.002, .003, .007)
and through it the published degree-data modules. No other M012 proof and
no unpublished declaration is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean`
(SHA-256 `a0b7ac8afcc55cad383a16e6dfe093e147770a7e8f5d21c3f8843744b57b7061`,
verified). The theorem is at lines 120–126, with its docstring at
lines 115–118 and its `@[simp]` attribute at line 119. The partition unit
M012.008 covers lines 120–129. The section variables are at line 27, inside
the `noncomputable section` (line 23) of namespace `ClassFormation`
(lines 17–228), with `namespace DegreeData` at lines 55–225. The complete
original is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean`.

| Original declaration | Adapted declaration |
| --- | --- |
| `ClassFormation.DegreeData.extensionRestriction_mk` (theorem) | `Langlands.NYLL.ClassFormation.DegreeData.extensionRestriction_mk` (theorem, this module) |
| Same theorem's statement | Existing `Langlands.NYLL.ClassFormation.DegreeData.extensionRestriction_mkStatement` |
| `ClassFormation.DegreeData.extensionRestriction` | Existing `Langlands.NYLL.ClassFormation.DegreeData.extensionRestriction` |

Modifications by Worker 5168 on 13 November 2026:

- add the `Langlands.NYLL` namespace prefix;
- give the theorem the published statement applied to its parameters as its
  type;
- write the normality binder with the Mathlib body
  `L.toSubgroup.subgroupOf K.toSubgroup` of the source abbreviation
  `CyclicCohomology.extensionSubgroup K L hLK`, as the published statement
  and definitions do;
- omit the `@[simp]` attribute, because the theorem's type is the statement
  constant rather than an equation;
- replace the source import with the sole Statements import and omit all
  other source declarations and the unused `open CyclicCohomology`.

The original docstring, the binder names and order, and the proof term
`rfl` are kept.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author "Naganori Yamaguchi (assisted by OpenAI
Codex)", Apache-2.0. The Lean file carries the dated modification record.
Worker 5168 adapted this proof from the pinned original. The published
statement and definitions and their Markdown are used unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are listed in
`repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This proves only M012.008. It discharges no class-formation, cup-product,
Tate, transfer or reciprocity target.
