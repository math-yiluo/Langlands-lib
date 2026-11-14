# NYLL M029: the infinite norm subgroup and the maximal-unramified norm subgroup

The paired Lean file ports three data definitions from the NYLL
norm-subgroup module:

- the norm image from one finite intermediate field;
- the infinite norm subgroup, the intersection of those images over all finite
  intermediate fields;
- the norm subgroup of the maximal unramified extension.

The source is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
(file SHA-256
`7d4c7c59cd25c27a728b49b8b4df61649bc818d2ef7ff4fdc375a92ea13f7460`). The
registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Units

Adapted names use the prefix `Langlands.NYLL.ClassFormation.`. Original
names use the prefix `ClassFormation.`. The line ranges include the
docstrings.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M029.003 | `finiteIntermediateNormRange` | 75–81 (declaration at 76) | `finiteIntermediateNormRange` |
| M029.004 | `infiniteNormSubgroup` | 83–90 (declaration at 86) | `infiniteNormSubgroup` |
| M029.024 | `DegreeData.maximalUnramifiedNormSubgroup` | 292–296 (declaration at 293) | `DegreeData.maximalUnramifiedNormSubgroup` |

The source context is as follows:

- Lines 20–28: `namespace ClassFormation`, the opens `KummerTheory` and
  `CyclicCohomology`, and `noncomputable section`.
- M029.003 and M029.004 lie in `section infiniteNorms` (line 70). Its
  variables are `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
  (line 73).
- M029.024 lies in `section maximalUnramifiedNorms` (line 285), with the same
  variables (line 288), inside `namespace DegreeData` (line 290).

## The declarations

Every declaration takes the implicit group `{G : IntegralRepGroupType}` and
the instance arguments `[Group G] [TopologicalSpace G]`. `IntegralRepGroupType`
is the Library's `Langlands.NYLL.IntegralRepGroupType` (M002.001), the alias
`Type 0`. It is needed because Mathlib's `Rep ℤ G` puts `G` in universe zero.
A field is represented contravariantly by a closed subgroup of `G`, of type
Mathlib's `ClosedSubgroup G`. `A : Rep ℤ G` is an integral representation,
and for a closed subgroup `H`, `ambientFixedAddSubgroup A H` is the Library's
`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (M023.001). That is the
additive subgroup `A_H` of vectors fixed by `H`. Mathlib's `Rep` carries a
separate universe for the carrier of the representation. In `Rep ℤ G` that
universe is left implicit, exactly as in the source, so Lean makes it an
automatic universe parameter (reported as `u_1`) of each declaration, as it
does for the Library's `relativeNorm`.

**`finiteIntermediateNormRange`** (M029.003) takes explicit
`(A : Rep ℤ G) (E K : ClosedSubgroup G) (M : FiniteIntermediateField E K)`
and returns an `AddSubgroup (ambientFixedAddSubgroup A K)`.

- `FiniteIntermediateField E K` is the Library structure
  `Langlands.NYLL.ClassFormation.FiniteIntermediateField` (M029.001). It
  consists of a closed subgroup `M.field` with `E ≤ M.field ≤ K`, given by the
  proof `M.below : M.field.toSubgroup ≤ K.toSubgroup`, together with finiteness
  of the coset space `G_K / G_M` (the field `M.finite`).
- The body is the source tactic block, kept verbatim. `letI := M.finite`
  installs that finiteness as an instance, and the result is the range of the
  Library's relative norm homomorphism
  `Langlands.NYLL.ClassFormation.relativeNorm A K M.field M.below :
  A_M →+ A_K` (M024.009), that is, the norm image `N_{M|K} A_M`.
- The Library's `relativeNorm` states its finiteness instance as
  `Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)`.
  `M.finite` states it with `extensionSubgroup K M.field M.below`. The
  Library's `extensionSubgroup` (M004.002) is an `abbrev` for exactly that
  `subgroupOf`, so instance search finds the installed instance without any
  change to the source body.

**`infiniteNormSubgroup`** (M029.004) takes explicit
`(A : Rep ℤ G) (E K : ClosedSubgroup G)` and returns the additive subgroup
`⨅ M : FiniteIntermediateField E K, finiteIntermediateNormRange A E K M` of
`A_K`. This is `N_{E|K} A_E = ⋂_M N_{M|K} A_M`, the intersection of the norm
images over all finite intermediate fields `M` of `E | K`, taken in the
complete lattice of additive subgroups.

**`DegreeData.maximalUnramifiedNormSubgroup`** (M029.024) takes explicit
`(D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)` and returns
`infiniteNormSubgroup A (D.maximalUnramifiedField L) K`. This is the infinite
norm subgroup of `A_K` for the extension whose top field is the maximal
unramified extension `\widetilde L` of `L`.

- `DegreeData` is the Library's `Langlands.NYLL.ClassFormation.DegreeData`
  (M010.002).
- `maximalUnramifiedField` is the Library's
  `Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedField`
  (M029.016), the closed subgroup `G_L ∩ ker d`.

## Modifications

Worker 5264 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`. The
  opens `KummerTheory` and `CyclicCohomology` resolve to the Library
  namespaces `Langlands.NYLL.KummerTheory` (for `ambientFixedAddSubgroup`) and
  `Langlands.NYLL.CyclicCohomology`.
- Only these three declarations are ported. Every other declaration of the
  source file is omitted from this module. M029.001, M029.002 and M029.016 are
  already in the Library module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`,
  which this file imports. The remaining units of the source file belong to
  separate tasks.
- `universe u` (source line 18) is omitted. None of the three declarations
  uses it, because their group is `G : IntegralRepGroupType`.
- The two sections, their `variable` lines and comments, and the
  `namespace DegreeData` block are kept with the same names and binders. Every
  telescope is therefore unchanged.
- The source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements`
  and `Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` are replaced by two
  focused Library imports:
  - `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`,
    for `FiniteIntermediateField`, `maximalUnramifiedField` and, through its
    imports, `DegreeData` and `extensionSubgroup`;
  - `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`,
    for `relativeNorm` and, through its imports, `ambientFixedAddSubgroup` and
    `IntegralRepGroupType`.

The binders, binder kinds, docstrings and bodies are otherwise unchanged,
including the tactic body of `finiteIntermediateNormRange`. A focused
`lean_check` of this module reports no errors or warnings. Its inspection of
`maximalUnramifiedNormSubgroup` reports the single universe parameter `u_1`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

These are data definitions only. No norm-subgroup, reciprocity,
class-formation or cohomological theorem is asserted here. The membership
characterizations M029.005 and M029.026 and the equation M029.025 are separate
statement units.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
