# NYLL M296.011: the named abelian quotient projection

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_applyStatement`
by the theorem
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply`,
the source name of M296.011 with the namespace prefix `Langlands.NYLL`. The
theorem's type is exactly that proposition applied to its two source
parameters, `extensionQuotientMk_applyStatement L k`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, implicit `G : Type u`, the instances
`[Group G]` and `[TopologicalSpace G]`, implicit `K : ClosedSubgroup G`,
explicit `L : FiniteAbelianSubextension K` and explicit `k : K.toSubgroup`.
These are the binders of the published proposition (the source section
variables of lines 40 and 52, then the theorem's own `L` and `k`), with the
same names, kinds, order and universe `u`. There is no `IsTopologicalGroup G`
hypothesis, and no finiteness, commutativity or closedness assumption is used
beyond the data carried by `L`.

Unfolding the published proposition gives

```lean
L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
  (QuotientGroup.mk k :
    K.toSubgroup ⧸ extensionSubgroup K L.field L.below)
```

that is: the canonical projection `K.toSubgroup →* L.extensionQuotient` of
the finite abelian extension `L`, read through the comparison equivalence
`L.extensionQuotient ≃* K.toSubgroup ⧸ extensionSubgroup K L.field L.below`,
sends `k` to its ordinary class in Mathlib's quotient group. Here
`extensionSubgroup K L.field L.below` is the published
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), an
abbreviation for `L.field.toSubgroup.subgroupOf K.toSubgroup`, the
subgroup `G_L` viewed inside `G_K`.

## Implemented proof

The complete proof body is

```lean
  rfl
```

The equation holds by definitional unfolding, in four steps, all through
published definitions:

1. `FiniteAbelianSubextension.extensionQuotientMulEquiv L` (M296.009) is
   by definition `L.toFiniteGaloisExtension.extensionQuotientMulEquiv`, and
   `FiniteAbelianSubextension.extensionQuotientMk L` (M296.010) is by
   definition `L.toFiniteGaloisExtension.extensionQuotientMk`. The
   abbreviations `L.field` and `L.below` (M296.002, .003) are likewise
   `L.toFiniteGaloisExtension.field` and `L.toFiniteGaloisExtension.below`,
   and `L.extensionQuotient` (M296.006) is
   `L.toFiniteGaloisExtension.extensionQuotient`.
2. For the underlying `FiniteGaloisSubextension K`, the comparison
   `extensionQuotientMulEquiv` (M040) is `MulEquiv.refl _`, its quotient
   `extensionQuotient` is `K.toSubgroup ⧸ extensionSubgroup K L.field L.below`,
   and its projection `extensionQuotientMk` is
   `QuotientGroup.mk' (extensionSubgroup K L.field L.below)`. Its normality
   argument is a proof of a proposition, so it does not affect the
   computation; that module derives it from `L.normal` by the published
   instance `FiniteGaloisSubextension.extensionSubgroup_normalInstance`.
3. Applying `MulEquiv.refl _` returns its argument, and
   `QuotientGroup.mk' N k` is `QuotientGroup.mk k` by definition.
4. Hence both sides are the same term, and `rfl` closes the goal, the
   published proposition being unfolded by the definitional check itself.

No auxiliary declaration, extra hypothesis, instance or `simp` registration is
introduced. The development check reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`, inherited from the imported Mathlib
quotient-group and closed-subgroup infrastructure; the `rfl` proof adds none.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_applyStatement`
  in `Reciprocity/FiniteAbelianSubextension/Statements` (unfolded only).
- The published M296 data `FiniteAbelianSubextension`, `field`, `below`,
  `extensionQuotient`, `extensionQuotientMulEquiv` and `extensionQuotientMk`
  in `Reciprocity/FiniteAbelianSubextension/Definitions`, and, beneath them,
  the published M040 data `FiniteGaloisSubextension.extensionQuotient`,
  `extensionQuotientMulEquiv`, `extensionQuotientMk` and
  `extensionSubgroup_normalInstance` in
  `Reciprocity/FiniteGaloisSubextension/Definitions`, all reached through the
  unchanged import chain.
- Mathlib's `MulEquiv.refl`, `QuotientGroup.mk'` and `QuotientGroup.mk`,
  reached through the same chain.

No other proof module is imported. In particular the proof does not use the
finite Galois lemma M040.012 (`FiniteGaloisSubextension.extensionQuotientMk_apply`,
whose target `FiniteGaloisSubextension.extensionQuotientMk_applyStatement` is
published but which this module does not need).

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:110–117`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean#L110-L117)
(whole-file SHA-256
`f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`). Line 110
is the retained docstring, line 111 the `@[simp]` attribute, lines 112–116
the signature and conclusion, and line 117 the proof term
`L.toFiniteGaloisExtension.extensionQuotientMk_apply k`. That term applies the
finite Galois lemma M040.012 of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
(lines 109–116, whole-file SHA-256
`c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`), whose own
proof at line 116 is `rfl`. Both hashes were recomputed by Worker 466 on
14 November 2026 UTC from the retained snapshot under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `FiniteAbelianSubextension.extensionQuotientMk_apply` (M296.011) | Published `FiniteAbelianSubextension.extensionQuotientMk_applyStatement` in `Reciprocity/FiniteAbelianSubextension/Statements` |
| Proof `FiniteAbelianSubextension.extensionQuotientMk_apply` | This theorem of the same adapted name in `Reciprocity/FiniteAbelianSubextension/U011/Proofs` |
| `FiniteAbelianSubextension.extensionQuotientMulEquiv`, `extensionQuotientMk` (M296.009, .010) | Existing published definitions in `Reciprocity/FiniteAbelianSubextension/Definitions` |

The adaptation makes these changes:

1. The namespace is prefixed with `Langlands.NYLL`, and the original imports
   are replaced by the sole published `FiniteAbelianSubextension.Statements`
   import.
2. The theorem's type is the published proposition applied to `L k`, rather
   than the spelled-out equation; the two are definitionally equal.
3. The proof term `L.toFiniteGaloisExtension.extensionQuotientMk_apply k` is
   replaced by `rfl`, the body of the finite Galois lemma it invokes, so that
   the proof needs no unpublished or separately reviewed M040.012 proof. The
   proved proposition is unchanged.
4. The `@[simp]` attribute of line 111 is omitted: the theorem's type is the
   named proposition, not a syntactic equation, so it would not be a useful
   simp lemma. The theorem is available for explicit application, and its
   statement can be unfolded to the equation.
5. Only the section variables used by this theorem are restated
   (`{G : Type u} [Group G] [TopologicalSpace G]` and `{K : ClosedSubgroup G}`,
   source lines 40 and 52); the `noncomputable section` and `open` lines are
   unnecessary and omitted. The docstring is the source docstring verbatim.

The [public partition](../../../../../../../notes/reuse/nyll-public-port/m289-m312.md#m296)
places this proof at M296.011, after M296.010.END and before M296.012, and its
suggested `Uxxx/Proofs.lean` layout gives this module's path. No patch10 edit
applies to M296. The sibling proofs M296.012 and M296.013 are separate
candidates and are neither used nor provided here.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 466's dated modification
record. Worker 466 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

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

This proof covers only M296.011. The quotient elimination principle
(M296.012), extensionality (M296.013), the field-inclusion order, compositum,
intersection and norm-subgroup assignment of the source file, and any
reciprocity or classification theorem are separate work.
