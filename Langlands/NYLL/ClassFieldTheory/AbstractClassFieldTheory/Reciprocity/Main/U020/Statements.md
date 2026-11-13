# Abelianized restriction on quotient representatives: statement

This module defines one closed proposition,
`Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction_of_mkStatement : Prop`,
the statement phase of source row M086.020, the theorem
`ClassFormation.normResidueNaturalityAbelianizedRestriction_of_mk`. The
module contains no proof. A separate proof child will prove it under the
name `Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction_of_mk`.

## Complete closed telescope

The definition has one universe parameter `u` (the source's `Type*`) and no
other parameters. Its body is

```lean
∀ {G : Type u} [Group G] [TopologicalSpace G]
  (K K' L L' : ClosedSubgroup G)
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
  (hK'K : K'.toSubgroup ≤ K.toSubgroup)
  (hL'L : L'.toSubgroup ≤ L.toSubgroup)
  [(Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK).Normal]
  [(Langlands.NYLL.CyclicCohomology.extensionSubgroup K' L' hL'K').Normal]
  (k' : K'.toSubgroup),
  normResidueNaturalityAbelianizedRestriction K K' L L'
      hLK hL'K' hK'K hL'L
      (Abelianization.of (QuotientGroup.mk k')) =
    Abelianization.of
      (QuotientGroup.mk (Subgroup.inclusion hK'K k'))
```

The binders are those of the source theorem, in the same order and with
the same binder kinds. The source names the two instance hypotheses
`hLnormal` and `hL'normal`; the conclusion does not mention them, so they
are anonymous here. The source's section variables (line 1000) are shadowed
by the theorem's own `G` and are not part of its telescope.

## Meaning

For closed subgroups `L ≤ K`, `L' ≤ K'` of a topological group `G` with
`K' ≤ K`, `L' ≤ L` and the two normality instances,
`normResidueNaturalityAbelianizedRestriction K K' L L' hLK hL'K' hK'K hL'L`
(M086.019) is the abelianized restriction map
`G(L'/K')ᵃᵇ →* G(L/K)ᵃᵇ`, where `G(L/K)` is
`K.toSubgroup ⧸ extensionSubgroup K L hLK`. The statement says that on the
class of a representative `k' ∈ K'` it is given by the inclusion
`K' ≤ K`: the class of `k'` in `G(L'/K')ᵃᵇ` goes to the class of `k'`,
viewed in `K` by `Subgroup.inclusion hK'K`, in `G(L/K)ᵃᵇ`.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M086.019, `ClassFormation.normResidueNaturalityAbelianizedRestriction` | `Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U019.Definitions` (the sole import) |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, reached through the import |
| Mathlib `Abelianization.of`, `QuotientGroup.mk`, `Subgroup.inclusion`, `ClosedSubgroup`, `Subgroup.Normal` | Used unchanged |

## Library search

The whole Library at commit `ccda47ce0341746db208ee15e862d9226cc25fcc` was
searched for `normResidueNaturality` and for `Abelianization.map` and
`Abelianization.of` together with `finiteReciprocityNaturalityRestriction`.
None occurs. So nothing in the Library already covers M086.020.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean>),
SHA-256 `6883a1db96a9baf23b9c4f040e635f10b7732f36c558d9e0a96faa88a2da854b`.
The header is at lines 1–5, the namespace `ClassFormation` at 26 and the
second `noncomputable section` with its `variable` line at 997 and 1000.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M086.020, `ClassFormation.normResidueNaturalityAbelianizedRestriction_of_mk` | docstring 1043–1047, `@[simp]` 1048, signature 1049–1063, proof 1064–1071 (omitted) | `Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction_of_mkStatement` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the asserted type directly from the pinned original on
13 November 2026 and made these changes:

- The theorem becomes a Prop-valued definition with the `Statement`
  suffix. All binders move inside the proposition in the same order and
  with the same binder kinds; `Type*` becomes the explicit universe `u`.
  The two unreferenced instance hypotheses become anonymous. The proof is
  omitted for the separate proof phase.
- The namespace `ClassFormation` gets the `Langlands.NYLL` prefix, and
  `extensionSubgroup` is written by its full published name.
- The source `@[simp]` attribute is not installed.
- The source imports are replaced by the single published M086.019 module.
- All other declarations of the source file are omitted.

The original docstring is kept. No instance or simp attribute is
installed. No shared draft or other worker's unpublished work was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this statement. Its truth proof belongs to a
separate proof unit published after the statement is accepted.
