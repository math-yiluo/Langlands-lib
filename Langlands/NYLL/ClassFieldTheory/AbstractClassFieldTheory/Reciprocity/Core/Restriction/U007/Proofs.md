# NYLL M075.007: surjectivity of the upper-row restriction

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.abstractReciprocityRestriction_surjectiveStatement`
by the theorem
`Langlands.NYLL.ClassFormation.abstractReciprocityRestriction_surjective`.
The theorem's type is exactly that proposition applied to its source
parameters, `abstractReciprocityRestriction_surjectiveStatement K M L hLM hMK`,
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
and `hMK : M.toSubgroup ≤ K.toSubgroup`, and the named instances
`hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal` and
`hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal`. The universe is
arbitrary. No finiteness, closedness beyond the `ClosedSubgroup` data, or
topological-group hypothesis is used.

Unfolding the published proposition gives

```lean
Function.Surjective (abstractReciprocityRestriction K M L hLM hMK)
```

Here `abstractReciprocityRestriction K M L hLM hMK` is the published
restriction `G(L/K) → G(M/K)` of M075.005 (`Core/Restriction/Definitions`),
the monoid homomorphism
`K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup →*
K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup` given by Mathlib's
`QuotientGroup.map` of the identity of `K.toSubgroup`. Surjectivity is
`Function.Surjective` of its underlying function: every class modulo `M`
is the image of a class modulo `L`.

## Implemented proof

The complete proof body is

```lean
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  exact ⟨QuotientGroup.mk k, rfl⟩
```

The first `intro q` unfolds the published proposition and
`Function.Surjective` and introduces an arbitrary class
`q : K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup`. Mathlib's
`QuotientGroup.induction_on` reduces the goal to classes
`QuotientGroup.mk k` of representatives `k : K.toSubgroup`. The class of the
same `k` modulo `L` is a preimage: the restriction sends it to
`QuotientGroup.mk k` by definitional computation of `QuotientGroup.map` on
representatives (the content of M075.006), so `rfl` closes the equation.

This is the original proof verbatim. No auxiliary declaration, extra
hypothesis, instance or `simp` registration is introduced, and the proof
does not import the M075.006 proof module: the computation is
definitional. The development check reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`, inherited from the imported
Mathlib quotient-group infrastructure.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction_surjectiveStatement`
  in `Core/Restriction/Statements` (unfolded only).
- The published definition
  `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction` in
  `Core/Restriction/Definitions`, reached through the unchanged import chain.
- Mathlib's `QuotientGroup.induction_on`, `QuotientGroup.mk`,
  `QuotientGroup.map` and `Function.Surjective`, reached through the same
  chain.

No other M075 proof is used, and the source abbreviation
`CyclicCohomology.extensionSubgroup` (M004.002) does not occur: the
published statement uses its defining Mathlib term.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean:492–505`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean#L492-L505).
Line 492 is the retained docstring, 493–501 the signature and conclusion,
and 502–505 the four tactic lines retained above. The restriction is
defined at lines 456–472 (M075.005). The section variable
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` at line 454 is
shadowed by the declaration's own `{G : Type*}` binder and is omitted. The
whole-file SHA-256 is
`0fc1bd5c66d628b74e079fd54af4a9df7334343e38186983257da5ce6a8f06fb`,
recomputed by Worker 9 on 13 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `abstractReciprocityRestriction_surjective` (M075.007) | Published `abstractReciprocityRestriction_surjectiveStatement` in `Core/Restriction/Statements` |
| Proof `abstractReciprocityRestriction_surjective` | This theorem of the same adapted name in `Core/Restriction/U007/Proofs` |
| `abstractReciprocityRestriction` (M075.005) | Existing published definition in `Core/Restriction/Definitions` |
| `extensionSubgroup K L h` (M004.002) | Its Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published `Core/Restriction/Statements` import
and states the theorem's type as the published proposition applied to
`K M L hLM hMK`; the proof text is unchanged. The
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m075)
places this proof at M075.007 after M075.006.END; no patch10 edit applies
to M075. The M075.009 proof depends on this result in the source; see its
own Markdown for how the port handles that.

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

This proof covers only M075.007. The representative computation
(M075.006), the same-base naturality comparison (M075.008), the finiteness
consequences (M075.009, M075.013), exactness of the upper row and any host
class-formation, transfer or reciprocity theorem are separate work.
