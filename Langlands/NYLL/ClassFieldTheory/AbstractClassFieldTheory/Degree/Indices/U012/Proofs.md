# NYLL M006.012: cardinal relative index at a finite coset boundary

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_eq_index_of_finiteStatement`
by the theorem
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_eq_index_of_finite`.
The theorem's type is exactly that proposition applied to its source
parameters, `relativeIndexCardinal_eq_index_of_finiteStatement hLK`, with the
implicit group, subgroups and finiteness instance supplied by elaboration.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U012.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, implicit `G : Type u`, the instance
`[Group G]`, implicit `L K : Subgroup G`, explicit `hLK : L ≤ K`, and the
instance `[Finite (K ⧸ L.subgroupOf K)]`. The universe `u` is arbitrary.
There is no normality premise on `L` or `K`, and no finiteness of `G` or
`K` is assumed: only the relative coset type `K ⧸ L.subgroupOf K` is
required to be finite.

Unfolding the published proposition gives

```lean
relativeIndexCardinal hLK = (L.relIndex K : Cardinal)
```

Here `relativeIndexCardinal hLK` is the published cardinal-valued relative
index from U010.Definitions. By definition it is
`intersectionIndexCardinal L K`, which is
`Cardinal.mk (K ⧸ L.subgroupOf K)`, the actual cardinality of the relative
left-coset type. The right side is Mathlib's natural-valued
`Subgroup.relIndex`, cast to `Cardinal.{u}`. Mathlib defines
`L.relIndex K` as `(L.subgroupOf K).index`, and `index` as the natural
cardinality `Nat.card (K ⧸ L.subgroupOf K)`, which is zero for an
infinite coset type. The equality therefore says that, at a finite coset
boundary, the cardinal index agrees with the natural one.

## Implemented proof

The complete proof body is

```lean
  rw [relativeIndexCardinal_eq_index_of_finiteStatement, relativeIndexCardinal,
    intersectionIndexCardinal, Subgroup.relIndex, Subgroup.index]
  exact Nat.cast_card.symm
```

The first rewrite unfolds the published proposition to its equality. The
next two rewrites unfold the published definitions `relativeIndexCardinal`
and `intersectionIndexCardinal`, turning the left side into
`Cardinal.mk (K ⧸ L.subgroupOf K)`. The rewrites by `Subgroup.relIndex` and
`Subgroup.index` turn the right side into
`((Nat.card (K ⧸ L.subgroupOf K) : ℕ) : Cardinal)`.
Mathlib's `Nat.cast_card` states that, for a finite type `α`,
`(Nat.card α : Cardinal) = Cardinal.mk α`; its finiteness hypothesis is
discharged by the theorem's instance `[Finite (K ⧸ L.subgroupOf K)]`.
Its symmetric form closes the goal.

Apart from the initial unfolding of the published proposition, this is the
original proof verbatim. No auxiliary declaration, extra hypothesis,
instance or `simp` registration is introduced. The development check
reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.relativeIndexCardinal_eq_index_of_finiteStatement`
  in U012.Statements (unfolded only).
- The published definitions
  `Langlands.NYLL.ClassFormation.relativeIndexCardinal` and
  `Langlands.NYLL.ClassFormation.intersectionIndexCardinal` in
  U010.Definitions, reached through the unchanged U012 import chain.
- Mathlib's `Subgroup.relIndex`, `Subgroup.index`
  (`Mathlib/GroupTheory/Index.lean`) and `Nat.cast_card`
  (`Mathlib/SetTheory/Cardinal/Finite.lean`), all available through the
  U012 statement module's imports.

No other M006 proof and no host class-formation or reciprocity theorem is
used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean:143–149`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean#L143-L149).
Lines 143–144 are the retained docstring, 145–147 the signature,
148 the rewrite by `relativeIndexCardinal`, `intersectionIndexCardinal`,
`Subgroup.relIndex` and `Subgroup.index`, and 149
`exact Nat.cast_card.symm`. The data it unfolds is at lines 131–141
(M006.010–011). The section at lines 23–25 declares universes `u v`,
`{G : Type u} {D : Type v} [Group G] [Group D]`; `D`, `[Group D]` and
`v` do not occur in this declaration and are omitted. The whole-file
SHA-256 is
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`,
recomputed by Worker 172 on 13 November 2026 UTC from the retained
snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `relativeIndexCardinal_eq_index_of_finite` (M006.012) | Published `relativeIndexCardinal_eq_index_of_finiteStatement` in U012.Statements |
| Proof `relativeIndexCardinal_eq_index_of_finite` | This theorem of the same adapted name in U012.Proofs |
| `intersectionIndexCardinal`, `relativeIndexCardinal` (M006.010–011) | Existing published definitions in U010.Definitions |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original import by the sole published U012.Statements import, states the
theorem's type as the published proposition applied to `hLK`, and prepends
the unfolding of that proposition to the original rewrite list. The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m006)
places this proof at M006.012 after M006.011.END.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 172's dated modification
record. Worker 172 extracted this proof directly from the pinned original
and the published statement. No unpublished project draft was reused, and
there are no project coauthors.

The unchanged inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M006.012. The cardinal laws M006.013–014, the
image–kernel laws M006.023–025 and any local reciprocity or host
class-formation theorem are separate work. Infinite cardinal indices are
untouched: the result says nothing when the coset type is infinite.
