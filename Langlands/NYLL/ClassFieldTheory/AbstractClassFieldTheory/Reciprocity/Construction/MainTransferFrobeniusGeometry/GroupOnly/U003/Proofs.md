# NYLL M068.003: normality of `L` in an intermediate field

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.transferNormNaturality_intermediateExtension_normalStatement`
by the theorem
`Langlands.NYLL.ClassFormation.transferNormNaturality_intermediateExtension_normal`.
The theorem's type is exactly that proposition applied to its source
parameters,
`transferNormNaturality_intermediateExtension_normalStatement K K' L hLK' hK'K`,
with the implicit group, its two structures and the normality instance
supplied by elaboration.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusGeometry.GroupOnly.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

As in the statement module, the section variables are
`{G : Type u} [Group G] [TopologicalSpace G]` for an arbitrary universe `u`.
The theorem then has, in this order, explicit closed subgroups
`K K' L : ClosedSubgroup G`, explicit `hLK' : L.toSubgroup ≤ K'.toSubgroup`
and `hK'K : K'.toSubgroup ≤ K.toSubgroup`, and the named instance
`hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal`.

Unfolding the published proposition gives

```lean
(L.toSubgroup.subgroupOf K'.toSubgroup).Normal
```

In the source's Galois language, where closed subgroups stand for the
absolute groups of fields and `L ≤ K' ≤ K` is a tower with base `K`,
intermediate field `K'` and top `L`: if `L | K` is normal, so is `L | K'`. As a
statement about groups, if `L` is normal in `K` (as a subgroup of `K`),
then `L` is normal in the intermediate subgroup `K'`. Only the
containment `K' ≤ K` enters the proof; `hLK'` is a source parameter that
the published proposition retains but the argument does not use.

## Implemented proof

The complete proof body is

```lean
  have hcomap : L.toSubgroup.subgroupOf K'.toSubgroup =
      (L.toSubgroup.subgroupOf K.toSubgroup).comap
        (Subgroup.inclusion hK'K) := by
    ext k'
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  rw [transferNormNaturality_intermediateExtension_normalStatement, hcomap]
  exact hLnormal.comap (Subgroup.inclusion hK'K)
```

1. **`hcomap`.** As subgroups of `K'`, `L ∩ K'` is the preimage of
   `L ∩ K` under Mathlib's inclusion homomorphism
   `Subgroup.inclusion hK'K : K'.toSubgroup →* K.toSubgroup`. By extension,
   for `k' : K'.toSubgroup`, `Subgroup.mem_comap` and two rewrites by
   Mathlib's `Subgroup.mem_subgroupOf` reduce membership on both sides to
   `(k' : G) ∈ L.toSubgroup` and
   `((Subgroup.inclusion hK'K k' : K.toSubgroup) : G) ∈ L.toSubgroup`.
   The inclusion does not change the underlying element of `G`, so the two
   sides agree definitionally and `rfl` closes the equivalence.
2. **Pull back normality.** Rewriting the goal first by the definition of
   the published proposition and then by `hcomap` turns it into normality
   of `(L.toSubgroup.subgroupOf K.toSubgroup).comap (Subgroup.inclusion hK'K)`.
   Mathlib's `Subgroup.Normal.comap` (the preimage of a normal subgroup
   under a group homomorphism is normal) applied to `hLnormal` closes it.

No auxiliary declaration, extra hypothesis, instance or `simp` registration
is introduced. The development check reports only the axioms `propext` and
`Quot.sound`.

### Adaptations

- The source proves `(extensionSubgroup K' L hLK').Normal`, with
  `CyclicCohomology.extensionSubgroup K L h` (M004.002) abbreviating
  `L.toSubgroup.subgroupOf K.toSubgroup`, and rewrites membership with
  `KummerTheory.mem_extensionSubgroup_iff` (M022.001, source
  `Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean`,
  lines 33–38, proof `Iff.rfl`). Neither is in the Library, and the
  published statement uses the expanded Mathlib term. The port writes the
  expanded subgroups in `hcomap` and rewrites with Mathlib's
  `Subgroup.mem_subgroupOf`, which states the same equivalence for the same
  subgroup.
- The final rewrite is preceded by unfolding
  `transferNormNaturality_intermediateExtension_normalStatement`, so that
  `hcomap` can rewrite the subgroup inside the goal.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.transferNormNaturality_intermediateExtension_normalStatement`
  in `Construction/MainTransferFrobeniusGeometry/GroupOnly/Statements`
  (unfolded only).
- Mathlib's `Subgroup.subgroupOf`, `Subgroup.comap`, `Subgroup.inclusion`,
  `Subgroup.mem_comap`, `Subgroup.mem_subgroupOf` and
  `Subgroup.Normal.comap`, reached through the import chain.

No other M068 declaration is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransferFrobeniusGeometry.lean:61–76`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransferFrobeniusGeometry.lean#L61-L76).
Line 61 is the retained docstring, 62–67 the signature and conclusion,
68–74 the `hcomap` step, 75 the rewrite by `hcomap` and 76 the final
`exact`. The universe `u` is declared at line 21 and the section variables
`{G : Type u} [Group G] [TopologicalSpace G]` at line 36, both retained.
The whole-file SHA-256 is
`fc8417e95ae9a1ac4186887f496d35b608cccae8d84670037d6cd874e03cf476`,
recomputed by Worker 9 on 13 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `transferNormNaturality_intermediateExtension_normal` (M068.003) | Published `transferNormNaturality_intermediateExtension_normalStatement` in `GroupOnly/Statements` |
| Proof `transferNormNaturality_intermediateExtension_normal` | This theorem of the same adapted name in `GroupOnly/U003/Proofs` |
| `KummerTheory.mem_extensionSubgroup_iff` (M022.001) | Mathlib `Subgroup.mem_subgroupOf` |
| `extensionSubgroup K L h` (M004.002) | Its Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published `GroupOnly/Statements` import,
states the theorem's type as the published proposition applied to
`K K' L hLK' hK'K`, and makes the replacements above. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m049-m072.md#m068)
places this proof at M068.003 after M068.002.END; no patch10 edit applies
to M068. This proof does not use M068.001–002.

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

The unchanged inherited [LICENSE](../../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
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

This proof covers only M068.003, a group-theoretic support lemma. The
Frobenius tower maps and orbit equivalences of M068.004 onward and any host
transfer, norm or reciprocity theorem are separate work.
