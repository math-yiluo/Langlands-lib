# NYLL M076: intermediate-extension subgroup and coset targets

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
(file SHA-256 `f031b91cd496accfb520a0665cbb59f5f8a4ac0f567ee2c5a5dffc408ef05b44`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Name map

All adapted names use the prefix
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.`, and all original
names the prefix `ClassFormation.FiniteGaloisSubextension.`. The source lines
are those of the theorem's binders and statement; the proof is omitted.

| Unit | Original theorem | Source lines | `omit` | Adapted Prop-valued target |
| --- | --- | --- | --- | --- |
| M076.002 | `mem_intermediateSubgroup_iff` | 51–54 | line 47 | `mem_intermediateSubgroup_iffStatement` |
| M076.006 | `mem_intermediateCoset_iff` | 86–89 | line 84 | `mem_intermediateCoset_iffStatement` |
| M076.009 | `intermediateSubgroup_eq_iUnion_cosets` | 139–142 | line 136 | `intermediateSubgroup_eq_iUnion_cosetsStatement` |
| M076.011 | `intermediateCoset_isClosed` | 165–166 | none | `intermediateCoset_isClosedStatement` |
| M076.012 | `intermediateSubgroup_isClosed` | 172–174 | none | `intermediateSubgroup_isClosedStatement` |
| M076.023 | `intermediateSubgroup_normal` | 297–299 | line 295 | `intermediateSubgroup_normalStatement` |
| M076.034 | `intermediateSubgroup_map_quotient_eq` | 460–462 | line 457 | `intermediateSubgroup_map_quotient_eqStatement` |

## Telescopes and statements

The source section is
`variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]`
(line 36) followed by `variable {K : ClosedSubgroup G}` (line 40). A source
theorem includes the instance `[IsTopologicalGroup G]` unless it is preceded
by `omit [IsTopologicalGroup G] in`. Hence the source telescope of
M076.011 and M076.012 is `{G : Type u_1} [Group G] [TopologicalSpace G]
[IsTopologicalGroup G] {K : ClosedSubgroup G}` followed by the theorem
binders, and that of the other five omits `[IsTopologicalGroup G]`.

A Prop-valued definition would drop an unused section instance, so the port
uses the section `variable {G : Type*} [Group G] [TopologicalSpace G]` and
writes `[IsTopologicalGroup G] {K : ClosedSubgroup G}` (M076.011, 012) or
`{K : ClosedSubgroup G}` (the others) as the first binders of each target.
This gives exactly the source telescopes, confirmed by a `#check` of each
target, with universe parameter `u_1`. The remaining binders and bodies, with
`(L : FiniteGaloisSubextension K)` written `(L)`, are:

- M076.002: `(L) (S : Subgroup L.extensionQuotient) (k : K.toSubgroup)`;
  `k ∈ L.intermediateSubgroup S ↔ L.extensionQuotientMk k ∈ S`.
- M076.006: `(L) (q : L.extensionQuotient) (x : K.toSubgroup)`;
  `x ∈ L.intermediateCoset q ↔ L.extensionQuotientMk x = q`.
- M076.009: `(L) (S : Subgroup L.extensionQuotient)`;
  `(L.intermediateSubgroup S : Set K.toSubgroup) =
  ⋃ q ∈ (S : Set L.extensionQuotient), L.intermediateCoset q`.
- M076.011: `(L) (q : L.extensionQuotient)`;
  `IsClosed (L.intermediateCoset q)`, for the subspace topology on
  `K.toSubgroup`.
- M076.012: `(L) (S : Subgroup L.extensionQuotient)`;
  `IsClosed (L.intermediateSubgroup S : Set K.toSubgroup)`.
- M076.023: `(L) (S : Subgroup L.extensionQuotient) (hS : S.Normal)`;
  `(L.intermediateSubgroup S).Normal`. The hypothesis `hS` is kept as an
  explicit binder although the conclusion does not mention it.
- M076.034: `(L) (S : Subgroup L.extensionQuotient)`;
  `(L.intermediateSubgroup S).map L.extensionQuotientMk = S`.

## Reused declarations

The data come from the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Definitions`
(`intermediateSubgroup`, M076.001; `intermediateCoset`, M076.004), which
imports the M040 port defining `FiniteGaloisSubextension`,
`extensionQuotient` and `extensionQuotientMk`. Mathlib supplies
`IsTopologicalGroup`, `IsClosed`, `Subgroup.map`, `Subgroup.Normal` and the
indexed union.

## Modifications

Worker 4918 made only these changes:

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`,
   and the two source imports are replaced by the sibling `Definitions`
   port, which imports the M040 port and `Mathlib.Topology.Algebra.Group.Basic`.
   `open KummerTheory` (line 28) is dropped since no such namespace is
   imported and the statements use nothing from it; `open CyclicCohomology`
   is kept.
2. Each listed `theorem` becomes a `def … : Prop` whose name adds the suffix
   `Statement`; the binders are moved before the colon and the source statement
   becomes the body. The proofs, the `@[simp]` attribute of M076.002
   (line 50) and the `omit … in` commands are omitted.
3. The section instance `[IsTopologicalGroup G]` and the section variable
   `{K : ClosedSubgroup G}` are written as binders of each target, as
   described above, so that every target has the source telescope.
4. For M076.023, whose conclusion does not mention `hS`, the definition is
   preceded by `set_option linter.unusedVariables false in`; this only
   silences the linter.
5. Each docstring is the source docstring prefixed by `Target M076.xxx:`.
6. The source module docstring (lines 10–24) is replaced by a short
   docstring recording these modifications. The unlisted source theorems
   and data commands are not stated here.

No proof is supplied: each target is to be proved separately.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
