# Abelianized restriction in the norm/restriction naturality diagram: definition

This module defines one declaration,
`Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction`.
It adapts source row M086.019, the definition
`ClassFormation.normResidueNaturalityAbelianizedRestriction`, keeping its
docstring, binders and body unchanged. The definition installs no instance
and proves no theorem.

## Telescope

```lean
normResidueNaturalityAbelianizedRestriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    Abelianization
        (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K') →*
      Abelianization (K.toSubgroup ⧸ extensionSubgroup K L hLK)
```

`G` is a topological group in an arbitrary universe (`Type*`, one universe
parameter), as in the source. The source file also has section variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 1000), but
the definition binds its own `G`, which shadows them, so no section variable
is included. Inspection of the compiled declaration (`#check`) confirms the
telescope above, with exactly these binders.

| Parameter | Kind and meaning |
| --- | --- |
| `{G : Type*}`, `[Group G]`, `[TopologicalSpace G]` | Implicit topological group, the abstract absolute Galois group |
| `K K' L L' : ClosedSubgroup G` | Explicit closed subgroups, the abstract fields `K, K', L, L'` |
| `hLK`, `hL'K'`, `hK'K`, `hL'L` | Explicit inclusions `L ≤ K`, `L' ≤ K'`, `K' ≤ K`, `L' ≤ L` |
| `[hLnormal]`, `[hL'normal]` | Instance hypotheses that `L` is normal in `K` and `L'` is normal in `K'` (as subgroups of `K`, `K'`) |

## Meaning

`extensionSubgroup K L hLK` is `L` viewed as a subgroup of `K`
(`L.toSubgroup.subgroupOf K.toSubgroup`), so the quotient
`K.toSubgroup ⧸ extensionSubgroup K L hLK` is the abstract Galois group
`G(L/K)`; the normality instances give the quotients their group structure.
The published `finiteReciprocityNaturalityRestriction K K' L L' hLK hL'K' hK'K hL'L`
(M066.001) is the restriction homomorphism `G(L'/K') →* G(L/K)` induced by
the inclusion `K' ≤ K`, which maps `L'` into `L`.

The body is `Abelianization.map` of that homomorphism: the induced
homomorphism `G(L'/K')ᵃᵇ →* G(L/K)ᵃᵇ` of abelianizations. It is the
left vertical arrow, after abelianization, of the first reciprocity
naturality diagram (norm on fixed coefficients, restriction on Galois
groups).

The published restriction map writes its quotients with
`L.toSubgroup.subgroupOf K.toSubgroup`, the body of the reducible
abbreviation `extensionSubgroup K L hLK`, so it is applied unchanged.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |
| M066.001, `ClassFormation.finiteReciprocityNaturalityRestriction` | `Langlands.NYLL.ClassFormation.finiteReciprocityNaturalityRestriction`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.Restriction.Definitions` |
| Mathlib `Abelianization`, `Abelianization.map`, `ClosedSubgroup`, `Subgroup.Normal` | Used unchanged; `Mathlib.GroupTheory.Abelianization.Defs` is imported for `Abelianization` |

## Library search

The whole Library at commit `ccda47ce0341746db208ee15e862d9226cc25fcc` was
searched for `normResidueNaturality`, for every use of
`finiteReciprocityNaturalityRestriction`, and for `Abelianization.map` in
the NYLL port. There is no `normResidueNaturality` declaration and no
`Abelianization.map` anywhere under `Langlands/NYLL`; the restriction map is
used only in its own module, in the same-base restriction statements and in
`MainTransfer/Intermediate`, never abelianized. So nothing in the Library
already covers M086.019. Worker 5264 (Task 5264, M258 closure) confirmed
that M086.014–M086.031 are outside that closure and may be published by
Task 5799.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean>).
The file was read around the declaration and its section structure was
checked; its SHA-256 is
`6883a1db96a9baf23b9c4f040e635f10b7732f36c558d9e0a96faa88a2da854b`.
The header is at lines 1–5, the imports at 7–16, the module docstring at
18–24, the namespace `ClassFormation` at 26, the `open` lines at 28 and 30,
and the second `noncomputable section` with its `variable` line at 997 and
1000.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M086.019, `ClassFormation.normResidueNaturalityAbelianizedRestriction` | docstring 1026–1027, signature 1028–1039, body 1040–1041 | `Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the definition directly from the pinned original on
13 November 2026 and made these changes:

- The namespace `ClassFormation` gets the `Langlands.NYLL` prefix. The name,
  docstring, binders and body are unchanged.
- The source imports are replaced by `Mathlib.GroupTheory.Abelianization.Defs`
  and the two published modules listed above.
- The source `open` lines are replaced by
  `open Langlands.NYLL.CyclicCohomology` (for `extensionSubgroup`);
  `KummerTheory` is not used.
- The shadowed section variables are omitted. A local `noncomputable
  section` wraps the definition, as in the source.
- All other declarations of the source file are omitted.

No instance or simp attribute is installed. No shared draft or other
worker's unpublished work was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this definition. The theorem
`normResidueNaturalityAbelianizedRestriction_of_mk` (M086.020, line 1049)
and the other declarations of the source file are separate units.
