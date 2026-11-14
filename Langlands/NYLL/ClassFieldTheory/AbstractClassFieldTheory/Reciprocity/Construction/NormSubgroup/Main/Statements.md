# NYLL M029: targets for the infinite and maximal-unramified norm subgroups

This module publishes six closed Prop-valued statement targets. They are the
statement phase of six source theorems of the NYLL norm-subgroup module, and
the module contains no proof. Later `lean.proof@1` tasks prove each target
under the source theorem name with the prefix `Langlands.NYLL.`.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
(file SHA-256
`7d4c7c59cd25c27a728b49b8b4df61649bc818d2ef7ff4fdc375a92ea13f7460`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Original names have the prefix `ClassFormation.` and adapted names the prefix
`Langlands.NYLL.ClassFormation.`. Each adapted name is the original name with
`Statement` appended.

| Unit | Original theorem | Docstring, signature, proof lines | Adapted target |
| --- | --- | --- | --- |
| M029.005 | `mem_infiniteNormSubgroup_iff` | 92, 93–99, 100 | `mem_infiniteNormSubgroup_iffStatement` |
| M029.011 | `infiniteNormClass_eq_zero_iff` | 144, 145–150, 151–152 | `infiniteNormClass_eq_zero_iffStatement` |
| M029.015 | `infiniteNormQuotientLift_infiniteNormClass` | 184–185, 186–193, 194 | `infiniteNormQuotientLift_infiniteNormClassStatement` |
| M029.025 | `DegreeData.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup` | 298–299, 300–303, 304 | `DegreeData.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroupStatement` |
| M029.026 | `DegreeData.mem_maximalUnramifiedNormSubgroup_iff` | 306, 307–312, 313 | `DegreeData.mem_maximalUnramifiedNormSubgroup_iffStatement` |
| M029.032 | `DegreeData.maximalUnramifiedNormClass_eq_zero_iff` | 356, 357–362, 363–364 | `DegreeData.maximalUnramifiedNormClass_eq_zero_iffStatement` |

The signature lines include the `@[simp]` attribute line where the source has
one (M029.005, .011, .015, .026, .032).

The source context is kept:

- Lines 20–28: `namespace ClassFormation`, `open KummerTheory`,
  `open CyclicCohomology` and `noncomputable section`.
- M029.005, .011 and .015 lie in `section infiniteNorms` (line 70), with the
  variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
  (line 73).
- M029.025, .026 and .032 lie in `section maximalUnramifiedNorms` (line 285),
  with the same variables (line 288), inside `namespace DegreeData`
  (line 290).

## Notation

Every target takes the implicit group `{G : IntegralRepGroupType}` and the
instance arguments `[Group G] [TopologicalSpace G]`.

- `IntegralRepGroupType` is the Library's `Langlands.NYLL.IntegralRepGroupType`
  (M002.001), the alias `Type 0`.
- A field is represented contravariantly by a closed subgroup of `G`.
- `A : Rep ℤ G` is an integral representation and
  `ambientFixedAddSubgroup A K` is the additive subgroup `A_K` of vectors
  fixed by `K`.
- `finiteIntermediateNormRange A E K M` is the norm image `N_{M|K} A_M` in
  `A_K` of a finite intermediate field `M` of `E | K`.
- `infiniteNormSubgroup A E K` is `N_{E|K} A_E`, the infimum of these norm
  images over all `M : FiniteIntermediateField E K`.
- `D.maximalUnramifiedField L` is the closed subgroup `G_L ∩ ker d`
  representing the maximal unramified extension `\widetilde L`, and
  `D.maximalUnramifiedNormSubgroup A K L` is
  `infiniteNormSubgroup A (D.maximalUnramifiedField L) K`.
- `InfiniteNormQuotient`, `infiniteNormClass`, `infiniteNormQuotientLift`,
  `DegreeData.MaximalUnramifiedNormQuotient` and
  `DegreeData.maximalUnramifiedNormClass` are the quotients, class maps and
  lift of the paired definition module.

## The targets

Each target has the source theorem's telescope in the source order, and its
body is the source statement verbatim.

**`mem_infiniteNormSubgroup_iffStatement`** (M029.005), with explicit
`(A : Rep ℤ G) (E K : ClosedSubgroup G) (a : ambientFixedAddSubgroup A K)`:

```lean
a ∈ infiniteNormSubgroup A E K ↔
  ∀ M : FiniteIntermediateField E K,
    a ∈ finiteIntermediateNormRange A E K M
```

An element of `A_K` is an infinite norm exactly when it is a norm from every
finite intermediate field.

**`infiniteNormClass_eq_zero_iffStatement`** (M029.011), with the same
explicit arguments:

```lean
infiniteNormClass A E K a = 0 ↔
  a ∈ infiniteNormSubgroup A E K
```

The class of `a` in `A_K / N_{E|K} A_E` vanishes exactly when `a` lies in the
norm subgroup. The zero is that of the instance
`infiniteNormQuotientAddCommGroup`.

**`infiniteNormQuotientLift_infiniteNormClassStatement`** (M029.015), with
`{B : Type*} [AddCommGroup B]`, then explicit
`(A : Rep ℤ G) (E K : ClosedSubgroup G)`,
`(f : ambientFixedAddSubgroup A K →+ B)`,
`(hf : infiniteNormSubgroup A E K ≤ f.ker)` and
`(a : ambientFixedAddSubgroup A K)`:

```lean
infiniteNormQuotientLift A E K f hf (infiniteNormClass A E K a) = f a
```

The map induced on the quotient by an additive map `f` that kills the norm
subgroup sends the class of `a` to `f a`. The hypothesis `hf` is used in the
conclusion as the argument of `infiniteNormQuotientLift`.

**`DegreeData.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroupStatement`**
(M029.025), with explicit
`(D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)`:

```lean
D.maximalUnramifiedNormSubgroup A K L =
  infiniteNormSubgroup A (D.maximalUnramifiedField L) K
```

**`DegreeData.mem_maximalUnramifiedNormSubgroup_iffStatement`** (M029.026),
with explicit
`(D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
(a : ambientFixedAddSubgroup A K)`:

```lean
a ∈ D.maximalUnramifiedNormSubgroup A K L ↔
  a ∈ infiniteNormSubgroup A (D.maximalUnramifiedField L) K
```

**`DegreeData.maximalUnramifiedNormClass_eq_zero_iffStatement`** (M029.032),
with the same explicit arguments as M029.026:

```lean
D.maximalUnramifiedNormClass A K L a = 0 ↔
  a ∈ D.maximalUnramifiedNormSubgroup A K L
```

The class of `a` in `A_K / N_{\widetilde L|K} A_{\widetilde L}` vanishes
exactly when `a` lies in the maximal-unramified norm subgroup. The zero is
that of the instance `DegreeData.maximalUnramifiedNormQuotientAddCommGroup`.

Every binder of each target occurs in its body, so no hypothesis is unused.

## Reused Library declarations

The file imports one module,
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Main.Definitions`.
That module supplies M029.006, .007, .009, .014, .027, .028 and .030. Through
its import
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions`
it also supplies:

- `Langlands.NYLL.ClassFormation.finiteIntermediateNormRange` (M029.003);
- `Langlands.NYLL.ClassFormation.infiniteNormSubgroup` (M029.004);
- `Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedNormSubgroup`
  (M029.024);
- `Langlands.NYLL.ClassFormation.FiniteIntermediateField` (M029.001);
- `Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedField` (M029.016);
- `Langlands.NYLL.ClassFormation.DegreeData` (M010.002);
- `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (M023.001);
- `Langlands.NYLL.IntegralRepGroupType` (M002.001).

The source names are written unqualified, as in the source. Under the kept
namespace and `open KummerTheory` they resolve to these published
declarations.

## Modifications

Worker 171 made only these changes to the six source theorems:

1. Each theorem becomes a Prop-valued `def` named with the suffix
   `Statement`, whose body is the source statement. The proofs are omitted
   for the separate proof phase.
2. The `@[simp]` attributes are omitted, because a `def` is not a simp lemma.
3. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
4. The source imports are replaced by the single Library import named above.
5. Each docstring begins with `Target for M029.xxx.` and then repeats the
   source docstring.
6. The other source declarations are omitted, as is `universe u` (source
   line 18), which no target uses. The module docstring (source lines 10–16)
   is replaced by one recording these modifications.

## Focused check

A focused `lean_check` of this module reports no errors or warnings. A
private check, not part of this submission, restates each source theorem with
its source signature and its source proof:

- `simp [infiniteNormSubgroup]` (M029.005);
- `unfold infiniteNormClass InfiniteNormQuotient` followed by
  `exact QuotientAddGroup.eq_zero_iff a` (M029.011);
- `rfl` (M029.015 and M029.025);
- `rw` with the restated M029.025 (M029.026);
- `unfold maximalUnramifiedNormClass MaximalUnramifiedNormQuotient` followed by
  the restated M029.011 (M029.032).

All six compile, and each is accepted, without change, as a proof of the
corresponding target. The `#check` telescopes of the six targets are those
displayed above. This check is not a submitted proof.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line with its OpenAI Codex assistance and the Apache-2.0 notice. It
also records these modifications. See `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit discharges no host class-formation, cup, transfer, Tate or
reciprocity target.
