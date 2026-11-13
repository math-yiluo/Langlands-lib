# NYLL M377.005: equality from containment and equal finite indices

This module defines the single proposition
`Langlands.NYLL.LubinTate.subgroup_eq_of_le_of_index_eq_of_ne_zeroStatement.{u}`.
Its complete body is:

```lean
∀ {G : Type u} [Group G] {H N : Subgroup G},
  H ≤ N → H.index = N.index → H.index ≠ 0 → H = N
```

Thus any subgroup `H` contained in `N` is equal to `N` when their indices
in the same ambient group are equal and the index of `H` is nonzero.
The group may inhabit any universe `u`; it need not be finite or commutative,
and neither subgroup is required to be normal. Mathlib's `Subgroup.index`
is `Nat.card (G ⧸ H)` and is zero for infinite index, so `H.index ≠ 0`
is the essential finite-index condition. All three original hypotheses are
retained in their original order as implications within the proposition.
This is a statement definition; its truth is a separate proof obligation.

## Exact source correspondence

The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, pinned at commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The readable retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The selected file, relative to that root, is
`Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/StandardSubgroupIndex.lean`,
SHA-256 `09a3021fc016de44aa5717a06d80cfa849c2ec642f9301a93538f1bb184e42b8`.

| Source unit | Original declaration | Exact location | Adapted declaration |
| --- | --- | --- | --- |
| M377.005 | `LubinTate.subgroup_eq_of_le_of_index_eq_of_ne_zero` | declaration at line 124; complete signature at lines 124–128; source proof at lines 129–139 | `Langlands.NYLL.LubinTate.subgroup_eq_of_le_of_index_eq_of_ne_zeroStatement` |

Source lines 121–123 already explain the nonzero-index condition. Source
lines 125–127 give `{G : Type*} [Group G] {H N : Subgroup G}` followed by
`hHN : H ≤ N`, `hindex : H.index = N.index`, and
`hindex_ne : H.index ≠ 0`; line 128 gives the conclusion `H = N`.
The adaptation places this entire telescope inside a `def ... : Prop`.
`Type*` becomes the explicit arbitrary `Type u`. The proof-binder names become
anonymous implication binders; their types and order are unchanged.

The source's surrounding `K : Type`, `Field K`, `ValuativeRel K`,
`TopologicalSpace K`, and `IsNonarchimedeanLocalField K` variables at
lines 42–43 do not occur in this theorem's signature. Lean therefore omits
them from its telescope, and the extracted statement has no such parameters.
The unused namespace openings, scoped notation and `noncomputable section`
are also omitted. The namespace gains `Langlands.NYLL`, the name gains
`Statement`, and the original theorem proof is omitted. These are all the
adaptations; no other source declaration is included.

## Imports and reuse

The sole direct import is `Mathlib.GroupTheory.Index`, already imported at
source line 7. It supplies the existing `Group`, `Subgroup`, subgroup order
and `Subgroup.index` used in the signature. The separate
`Mathlib.SetTheory.Cardinal.Finite` and four NYLL imports at source lines
8–12 are unnecessary for this statement. No external repository is imported
or installed, and no new instance or supporting definition is introduced.

The nonzero-index interpretation is recorded by Mathlib's
`Subgroup.index_ne_zero_iff_finite`; the source proof uses
`Subgroup.FiniteIndex` and `Subgroup.index_strictAnti`. Those declarations
are neither additional hypotheses nor replacements for the target, and
no proof is included here. An exact-name search in the current Library and
pinned Mathlib found no existing declaration of this target.

The successful focused check used environment artifact
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, with this module alone and the
exact proposition declaration supplied for inspection. The check returned
`ok: true`, no errors or warnings, declaration kind `definition`, universe
parameter `u`, and `statement_returns_prop: true`. This verifies the reduced
import set and the Prop-valued declaration; it does not prove the proposition.

## Provenance and license

The registered original source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The pinned source was read directly; no applicable NYLL erratum was found
in the Library's `notes/errata/`.

The original Apache-2.0 copyright and author header is retained verbatim,
with a separate modification record naming Worker 332 and the adaptations.
The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained
unchanged and match the pinned originals. Their SHA-256 values are,
respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
