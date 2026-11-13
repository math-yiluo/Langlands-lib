# NYLL M075.006: restriction on quotient representatives

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.abstractReciprocityRestriction_mkStatement`
by the theorem
`Langlands.NYLL.ClassFormation.abstractReciprocityRestriction_mk`.
The theorem's type is exactly that proposition applied to its source
parameters, `abstractReciprocityRestriction_mkStatement K M L hLM hMK k`,
with the implicit group, its two structures and the two normality instances
supplied by elaboration.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, implicit `G : Type u_1`, the instances
`[Group G]` and `[TopologicalSpace G]`, explicit closed subgroups
`K M L : ClosedSubgroup G`, explicit `hLM : L.toSubgroup ≤ M.toSubgroup`
and `hMK : M.toSubgroup ≤ K.toSubgroup`, the named instances
`hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal` and
`hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal`, and an explicit
element `k : K.toSubgroup`. The universe is arbitrary.

Unfolding the published proposition gives

```lean
abstractReciprocityRestriction K M L hLM hMK (QuotientGroup.mk k) =
  QuotientGroup.mk k
```

Here `abstractReciprocityRestriction K M L hLM hMK` is the published
restriction `G(L/K) → G(M/K)` of M075.005 (`Core/Restriction/Definitions`),
the monoid homomorphism
`K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup →*
K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup` defined by Mathlib's
`QuotientGroup.map` applied to the identity of `K.toSubgroup`, with the
compatibility `L ≤ M` supplied by `hLM`. The left `QuotientGroup.mk k` is the
class of `k` modulo `L`, the right one its class modulo `M`. The statement
says that restriction is computed on representatives: it is the identity on
`K`, read in the coarser quotient.

## Implemented proof

The complete proof body is

```lean
  rfl
```

`QuotientGroup.map N M f h (QuotientGroup.mk k)` reduces by definition to
`QuotientGroup.mk (f k)`: Mathlib defines `QuotientGroup.map` as
`QuotientGroup.lift` of `(QuotientGroup.mk' M).comp f`, itself a lift through
the quotient congruence, which computes on representatives (Mathlib's own
`QuotientGroup.map_mk` is proved by `rfl`). Here `f` is
`MonoidHom.id K.toSubgroup`, so `f k` is `k` definitionally. The published proposition is a `def` whose body
is this equation, so the kernel unfolds it as well. This is the original
proof term verbatim.

No auxiliary declaration, extra hypothesis, instance or `simp` registration
is introduced. The development check reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`, inherited from the imported
Mathlib quotient-group infrastructure.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction_mkStatement`
  in `Core/Restriction/Statements` (unfolded only).
- The published definition
  `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction` in
  `Core/Restriction/Definitions`, reached through the unchanged import chain.
- Mathlib's `QuotientGroup.map`, `QuotientGroup.mk`, `MonoidHom.id`,
  `Subgroup.subgroupOf` and `ClosedSubgroup`, reached through the same chain.

No other M075 proof is used. In particular the source abbreviation
`CyclicCohomology.extensionSubgroup` (M004.002) does not occur: the
published statement uses its defining Mathlib term
`L.toSubgroup.subgroupOf K.toSubgroup`.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean:474–490`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean#L474-L490).
Lines 474–477 are the retained docstring, 478 the `@[simp]` attribute,
479–489 the signature and conclusion, and 490 the proof `rfl`. The
restriction it computes is defined at lines 456–472 (M075.005). The section
variable `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` at
line 454 is shadowed by the declaration's own `{G : Type*}` binder and is
omitted. The whole-file SHA-256 is
`0fc1bd5c66d628b74e079fd54af4a9df7334343e38186983257da5ce6a8f06fb`,
recomputed by Worker 9 on 13 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `abstractReciprocityRestriction_mk` (M075.006) | Published `abstractReciprocityRestriction_mkStatement` in `Core/Restriction/Statements` |
| Proof `abstractReciprocityRestriction_mk` | This theorem of the same adapted name in `Core/Restriction/U006/Proofs` |
| `abstractReciprocityRestriction` (M075.005) | Existing published definition in `Core/Restriction/Definitions` |
| `extensionSubgroup K L h` (M004.002) | Its Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published `Core/Restriction/Statements` import
and states the theorem's type as the published proposition applied to
`K M L hLM hMK k`. The source `@[simp]` attribute is omitted: the adapted
theorem's type is the proposition `abstractReciprocityRestriction_mkStatement …`,
not a bare equation, so it would not serve as the source rewrite rule.
The [public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m075)
places this proof at M075.006 after M075.005.END; no patch10 edit applies
to M075.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 9's dated modification
record. Worker 9 extracted this proof directly from the pinned original
and the published statement. No unpublished project draft was reused, and
there are no project coauthors.

The unchanged inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained, with
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

This proof covers only M075.006. Surjectivity (M075.007), the same-base
naturality comparison (M075.008), the finiteness consequences
(M075.009, M075.013), exactness of the upper row and any host
class-formation, transfer or reciprocity theorem are separate work.
