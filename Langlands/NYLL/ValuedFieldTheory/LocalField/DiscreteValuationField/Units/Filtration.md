# NYLL M120: antitone subgroup filtration data

This module preserves the generic source structure: an antitone family of
subgroups of an arbitrary group, together with its named level accessor.
The interface alone asserts no valued-field semantics.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean` (M120).
The original file SHA-256 is
`30ce59edb8590e15afdaaef8d9551282e240c576f09be0ad55d12b09e9e4d807`.
The readable original is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean`
under registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original declaration | Source declaration lines | Adapted declaration |
| --- | --- | --- | --- |
| M120.001 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration` | 28–32 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration` |
| M120.002 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubgroup` | 39–40 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubgroup` |

The original structure docstring is at lines 26–27; its source context is
`namespace LocalFieldTheory`, `universe u v`, `open scoped BigOperators`,
`namespace DiscreteValuationField`. The accessor is in the structure's
namespace, under `variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)`
(lines 34–36).

## Complete construction and modifications

```lean
structure AntitoneSubgroupFiltration (G : Type u) [Group G] where
  subgroup : ℕ → Subgroup G
  antitone : ∀ {m n : ℕ}, m ≤ n → subgroup n ≤ subgroup m

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

def principalUnitSubgroup (n : ℕ) : Subgroup G :=
  U.subgroup n
```

The structure has one arbitrary carrier universe `u`; the unused source
universe declaration `v` is also retained. Its carrier binder is explicit,
followed by the group instance. The accessor keeps the implicit carrier,
group instance, explicit filtration and explicit natural-number level, in
that order. Both structure fields, their order and types, the declaration
bodies and their original docstrings are unchanged.

The only changes are the `Langlands.NYLL` namespace prefix, extraction of
these two declarations into this paired module, and the new module-level
modification note. The three source imports are retained verbatim:
`Mathlib.SetTheory.Cardinal.Finite`, `Mathlib.GroupTheory.Index`, and
`Mathlib.GroupTheory.QuotientGroup.Basic`. No source theorem is needed by
these data. The structure's generated fields and recursors remain attached
to it under the prefixed name.

The current Library and Mathlib were searched for the exact declarations
before this extraction. The named source interface is absent; the existing
Mathlib `Subgroup` is reused directly. In particular, lexical matches to
`ClassFormation.DegreeData.AbstractExtension.subgroup` and
`ClassFormation.DegreeData.FiniteAbstractExtension.subgroup` are unrelated.
No instance or external-module substitute is added here.

## Attribution and scope

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, Apache-2.0, author Naganori Yamaguchi (assisted by
OpenAI Codex). The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The public inventory records no patch10 modification for M120. Worker 321
made the extraction and namespace/import changes described above, without
reusing another worker's draft or compatibility patch.

These are data definitions, with no theorem target or proof publication in
this pair. They assert no reciprocity, class-formation, Tate, cup-product
or transfer result.
