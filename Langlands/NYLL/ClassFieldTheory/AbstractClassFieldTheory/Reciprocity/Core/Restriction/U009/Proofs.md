# NYLL M075.009: finiteness of the intermediate quotient

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.abstractReciprocity_intermediateQuotient_finiteStatement`
by the theorem
`Langlands.NYLL.ClassFormation.abstractReciprocity_intermediateQuotient_finite`.
The theorem's type is exactly that proposition applied to its source
parameters,
`abstractReciprocity_intermediateQuotient_finiteStatement K M L hLM hMK`,
with the implicit group, its two structures, the two normality instances
and the finiteness instance supplied by elaboration.

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
`hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal`, and the named
instance
`hLfinite : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)`.
The universe is arbitrary.

Unfolding the published proposition gives

```lean
Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup)
```

that is, the quotient `G(M/K)` of `K` by `M` (viewed as a subgroup of `K`)
is a finite type, given that `G(L/K)` is. Neither `G`, `K` nor any other
quotient is assumed finite.

## Implemented proof

The complete proof body is

```lean
  Finite.of_surjective (abstractReciprocityRestriction K M L hLM hMK) (by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro k
    exact ⟨QuotientGroup.mk k, rfl⟩)
```

Mathlib's `Finite.of_surjective` states that the codomain of a surjective
function out of a finite type is finite. It is applied to the underlying
function of the published restriction
`abstractReciprocityRestriction K M L hLM hMK :
K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup →*
K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup` (M075.005); finiteness
of its domain is the instance `hLfinite`. The term's type
`Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup)` is the
published proposition after unfolding its `def`.

The surjectivity argument in parentheses is the original proof of M075.007
(`abstractReciprocityRestriction_surjective`), reproduced verbatim: introduce
a class `q` modulo `M`, reduce by `QuotientGroup.induction_on` to a class
`QuotientGroup.mk k` of a representative `k : K.toSubgroup`, and give the
class of the same `k` modulo `L` as preimage; the restriction sends it to
`QuotientGroup.mk k` definitionally, so `rfl` closes the equation.

No auxiliary declaration, extra hypothesis, instance or `simp` registration
is introduced. The development check reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

### Adaptation: inlined surjectivity

The source proof (lines 538–539) is
`Finite.of_surjective (abstractReciprocityRestriction K M L hLM hMK)
(abstractReciprocityRestriction_surjective K M L hLM hMK)`, citing the
M075.007 theorem. That theorem is proved in this same task by the sibling
module `Core/Restriction/U007/Proofs`, which is not yet in the Library. As
the task directs, the port does not wait for it and does not publish a
second copy under its name: the four tactic lines of the M075.007 proof
(source lines 502–505) are supplied inline as an anonymous proof term. The
mathematical route is unchanged. Once M075.007 is published, the inline
argument could be replaced by a citation of
`Langlands.NYLL.ClassFormation.abstractReciprocityRestriction_surjective`
without changing this theorem's type.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.abstractReciprocity_intermediateQuotient_finiteStatement`
  in `Core/Restriction/Statements` (its type is the target).
- The published definition
  `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction` in
  `Core/Restriction/Definitions`, reached through the unchanged import chain.
- Mathlib's `Finite.of_surjective`, `QuotientGroup.induction_on` and
  `QuotientGroup.mk`, reached through the same chain.

No other M075 proof module is imported, and the source abbreviation
`CyclicCohomology.extensionSubgroup` (M004.002) does not occur: the
published statement uses its defining Mathlib term.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean:525–539`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean#L525-L539).
Lines 525–526 are the retained docstring, 527–537 the signature and
conclusion, and 538–539 the proof term. The inlined surjectivity proof is
at lines 502–505 (M075.007) and the restriction at lines 456–472
(M075.005). The section variable
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` at line 454 is
shadowed by the declaration's own `{G : Type*}` binder and is omitted. The
whole-file SHA-256 is
`0fc1bd5c66d628b74e079fd54af4a9df7334343e38186983257da5ce6a8f06fb`,
recomputed by Worker 9 on 13 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `abstractReciprocity_intermediateQuotient_finite` (M075.009) | Published `abstractReciprocity_intermediateQuotient_finiteStatement` in `Core/Restriction/Statements` |
| Proof `abstractReciprocity_intermediateQuotient_finite` | This theorem of the same adapted name in `Core/Restriction/U009/Proofs` |
| Citation of `abstractReciprocityRestriction_surjective` (M075.007) | Its four-line proof, inlined as an anonymous term |
| `abstractReciprocityRestriction` (M075.005) | Existing published definition in `Core/Restriction/Definitions` |
| `extensionSubgroup K L h` (M004.002) | Its Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published `Core/Restriction/Statements` import,
states the theorem's type as the published proposition applied to
`K M L hLM hMK`, and inlines the M075.007 proof as described above. The
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m075)
places this proof at M075.009 after M075.008.END; no patch10 edit applies
to M075. This proof does not depend on M075.008.

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

This proof covers only M075.009. Finiteness of `G(L/M)` (M075.013),
exactness of the upper row, the norm-subgroup comparisons and any host
class-formation, transfer or reciprocity theorem are separate work.
