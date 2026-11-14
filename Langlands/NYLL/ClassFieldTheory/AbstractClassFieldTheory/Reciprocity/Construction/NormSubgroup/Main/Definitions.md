# NYLL M029: the infinite and maximal-unramified norm quotients

The paired Lean file ports seven data declarations from the NYLL
norm-subgroup module:

- the quotient `A_K / N_{E|K} A_E` of a fixed module by an infinite norm
  subgroup, its additive group structure, its class map and its lifting
  property for additive maps;
- the corresponding quotient `A_K / N_{\widetilde L|K} A_{\widetilde L}` for
  the maximal unramified extension `\widetilde L` of `L`, with its additive
  group structure and its class map.

The source is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
(file SHA-256
`7d4c7c59cd25c27a728b49b8b4df61649bc818d2ef7ff4fdc375a92ea13f7460`). The
registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Units

Adapted names use the prefix `Langlands.NYLL.ClassFormation.`. Original
names use the prefix `ClassFormation.`. The adapted name is the original
name in both cases. The line ranges include the docstrings.

| Unit | Kind | Original name | Source lines (declaration line) |
| --- | --- | --- | --- |
| M029.006 | def | `InfiniteNormQuotient` | 102–109 (107) |
| M029.007 | instance | `infiniteNormQuotientAddCommGroup` | 111–116 (112) |
| M029.009 | def | `infiniteNormClass` | 126–132 (127) |
| M029.014 | def | `infiniteNormQuotientLift` | 174–182 (175) |
| M029.027 | def | `DegreeData.MaximalUnramifiedNormQuotient` | 315–321 (319) |
| M029.028 | instance | `DegreeData.maximalUnramifiedNormQuotientAddCommGroup` | 323–328 (324) |
| M029.030 | def | `DegreeData.maximalUnramifiedNormClass` | 338–344 (339) |

The source context is as follows:

- Lines 20–28: `namespace ClassFormation`, the opens `KummerTheory` and
  `CyclicCohomology`, and `noncomputable section`.
- M029.006, .007, .009 and .014 lie in `section infiniteNorms` (lines
  70–196). Its variables are
  `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 73).
- M029.027, .028 and .030 lie in `section maximalUnramifiedNorms` (lines
  285–417), with the same variables (line 288), inside `namespace DegreeData`
  (lines 290–415).

## The declarations

Every declaration takes the implicit group `{G : IntegralRepGroupType}` and
the instance arguments `[Group G] [TopologicalSpace G]`.

- `IntegralRepGroupType` is the Library's `Langlands.NYLL.IntegralRepGroupType`
  (M002.001), the alias `Type 0`. Mathlib's `Rep ℤ G` puts `G` in universe
  zero.
- A field is represented contravariantly by a closed subgroup of `G`, of type
  Mathlib's `ClosedSubgroup G`.
- `A : Rep ℤ G` is an integral representation. For a closed subgroup `H`,
  `ambientFixedAddSubgroup A H` is the Library's
  `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (M023.001), the
  additive subgroup `A_H` of vectors fixed by `H`.
- `infiniteNormSubgroup A E K` is the Library's
  `Langlands.NYLL.ClassFormation.infiniteNormSubgroup` (M029.004): the
  additive subgroup `N_{E|K} A_E` of `A_K`, the infimum over all finite
  intermediate fields `M` of `E | K` of the norm images `N_{M|K} A_M`.
- The carrier universe of `Rep ℤ G` is left implicit, exactly as in the
  source, so Lean makes it an automatic universe parameter. The quotients
  below live in that universe, reported as `Type u_1`.

**`InfiniteNormQuotient`** (M029.006) takes explicit
`(A : Rep ℤ G) (E K : ClosedSubgroup G)`. Its body is the quotient
`ambientFixedAddSubgroup A K ⧸ infiniteNormSubgroup A E K`, that is,
`A_K / N_{E|K} A_E`. It is a plain `def`, as in the source, so the quotient
structure is not visible to instance search. The source docstring says that
clients should go through the class map and the lift.

**`infiniteNormQuotientAddCommGroup`** (M029.007) is a global instance with the
same explicit arguments. It gives `AddCommGroup (InfiniteNormQuotient A E K)`
by the source tactic body `unfold InfiniteNormQuotient; infer_instance`, that
is, the quotient additive group structure of Mathlib. The instance is on the
new type `InfiniteNormQuotient`, so it overlaps no Mathlib or Library
instance.

**`infiniteNormClass`** (M029.009) takes the same arguments and is the
additive homomorphism `A_K →+ InfiniteNormQuotient A E K`. Its source tactic
body unfolds the quotient and gives
`QuotientAddGroup.mk' (infiniteNormSubgroup A E K)`, the canonical projection.

**`infiniteNormQuotientLift`** (M029.014) takes
`{B : Type*} [AddCommGroup B]`, then explicit
`(A : Rep ℤ G) (E K : ClosedSubgroup G)`, an additive homomorphism
`(f : ambientFixedAddSubgroup A K →+ B)` and the proof
`(hf : infiniteNormSubgroup A E K ≤ f.ker)`. It returns
`InfiniteNormQuotient A E K →+ B`. Its source tactic body unfolds the
quotient and gives `QuotientAddGroup.lift (infiniteNormSubgroup A E K) f hf`,
the map induced by `f` on the quotient. The `Type*` binder makes a second
universe parameter, so the declaration has the two universe parameters
`u_1` (of `B`) and `u_2` (the carrier of `A`).

**`DegreeData.MaximalUnramifiedNormQuotient`** (M029.027) takes explicit
`(D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)`. Its body is
`InfiniteNormQuotient A (D.maximalUnramifiedField L) K`, the quotient of
`A_K` by the infinite norm subgroup for the extension `\widetilde L | K`.

- `DegreeData` is the Library's `Langlands.NYLL.ClassFormation.DegreeData`
  (M010.002).
- `maximalUnramifiedField` is the Library's
  `Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedField`
  (M029.016), the closed subgroup `G_L ∩ ker d` representing `\widetilde L`.
- It is again a plain `def`. The source docstring says it is not a
  reducible alias for the infinite norm quotient.

**`DegreeData.maximalUnramifiedNormQuotientAddCommGroup`** (M029.028) is a
global instance with the same explicit arguments. It gives
`AddCommGroup (D.MaximalUnramifiedNormQuotient A K L)` by the source tactic
body `unfold MaximalUnramifiedNormQuotient; infer_instance`. Instance search
then finds `infiniteNormQuotientAddCommGroup`. This instance is also on a new
type.

**`DegreeData.maximalUnramifiedNormClass`** (M029.030) takes the same
arguments and is the additive homomorphism
`A_K →+ D.MaximalUnramifiedNormQuotient A K L`. Its source tactic body unfolds
the quotient and gives
`infiniteNormClass A (D.maximalUnramifiedField L) K`.

## Reused Library declarations

The file imports one module,
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions`.
That module contains `infiniteNormSubgroup` (M029.004). Through its imports it
also supplies the other Library declarations named above:
`IntegralRepGroupType`, `ambientFixedAddSubgroup`, `DegreeData` and
`maximalUnramifiedField`.

This module never ports a second copy of `finiteIntermediateNormRange`,
`infiniteNormSubgroup` or `DegreeData.maximalUnramifiedNormSubgroup`
(M029.003, M029.004, M029.024).

## Modifications

Worker 171 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`. The
  opens `KummerTheory` and `CyclicCohomology` are kept. They resolve to the
  Library namespaces `Langlands.NYLL.KummerTheory` (for
  `ambientFixedAddSubgroup`) and `Langlands.NYLL.CyclicCohomology`.
- The source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements`
  and `Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` are replaced by the
  single Library import named above.
- Only these seven declarations are ported. The source file's other
  declarations are left out:
  - M029.001–.004, .016 and .024 are already in the Library and are imported.
  - The theorems M029.005, .011, .015, .025, .026 and .032 are published as
    Prop-valued targets in the separate module
    `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Main.Statements`.
  - The remaining declarations, including the equivalences
    `infiniteNormQuotientConcreteEquiv` and
    `DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv` and the second
    lift `DegreeData.maximalUnramifiedNormQuotientLift`, are not units of
    this task. None of the seven ported declarations depends on them.
- `universe u` (source line 18) is omitted. None of the seven declarations
  uses it, because their group is `G : IntegralRepGroupType`.
- The two sections, their `variable` lines and comments, and the
  `namespace DegreeData` block are kept with the same names and binders. Every
  telescope is therefore unchanged.

The binders, binder kinds, docstrings and tactic bodies are otherwise
unchanged. The two instances keep their source scope: they are global
instances in the namespace `Langlands.NYLL.ClassFormation` (respectively
`Langlands.NYLL.ClassFormation.DegreeData`), as in the source.

## Focused check

A focused `lean_check` of this module reports no errors or warnings. Its
inspection of `infiniteNormQuotientLift` reports the universe parameters
`u_1` and `u_2` and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. A private check, not part of this submission, compiles with no
errors or warnings and confirms the following by `rfl`:

- `infiniteNormClass A E K a` is
  `QuotientAddGroup.mk' (infiniteNormSubgroup A E K) a`, read in
  `ambientFixedAddSubgroup A K ⧸ infiniteNormSubgroup A E K`;
- `infiniteNormQuotientAddCommGroup A E K` is Mathlib's
  `QuotientAddGroup.Quotient.addCommGroup (infiniteNormSubgroup A E K)`;
- `D.maximalUnramifiedNormQuotientAddCommGroup A K L` is
  `infiniteNormQuotientAddCommGroup A (D.maximalUnramifiedField L) K`;
- `D.maximalUnramifiedNormClass A K L a` is
  `infiniteNormClass A (D.maximalUnramifiedField L) K a`;
- `infiniteNormQuotientLift A E K f hf (infiniteNormClass A E K a)` is
  `f a` (the source `rfl` proof of M029.015).

The same check also replays, on the ported definitions, the source tactic
bodies of two declarations that are not ported here: M029.008
(`infiniteNormQuotientConcreteEquiv`) and M029.035
(`DegreeData.maximalUnramifiedNormQuotientLift`).

## Scope

These are data definitions and instances only. No norm-subgroup, reciprocity,
class-formation or cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
