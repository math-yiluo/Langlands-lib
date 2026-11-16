# NYLL M029.035: the lift out of the maximal-unramified norm quotient

The paired Lean file adapts one definition of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`.
The pinned source file has SHA-256
`7d4c7c59cd25c27a728b49b8b4df61649bc818d2ef7ff4fdc375a92ea13f7460`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.DegreeData.` | Docstring | Header | Body | Adapted name after `Langlands.NYLL.ClassFormation.DegreeData.` |
| --- | --- | --- | --- | --- | --- |
| M029.035 | `maximalUnramifiedNormQuotientLift` | 386 | 387–392 | 393–396 | `maximalUnramifiedNormQuotientLift` |

The source file imports
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements` and
`Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` (lines 7–8). The context
is `universe u` (line 18), `namespace ClassFormation` (line 20),
`open KummerTheory` (line 22), `open CyclicCohomology` (line 24),
`noncomputable section` (line 28), the section `maximalUnramifiedNorms`
(lines 285 and 417) with the comment and variable lines 287–288,

```lean
-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
```

`namespace DegreeData` (lines 290 and 415) and the closing lines 419–420.
The port keeps this context in the same order and omits `universe u`, which
the section does not use.

The names used resolve to published `Langlands.NYLL` declarations, all
imported through `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Main.Definitions`:
`ClassFormation.DegreeData` (M010.002) and the maximal unramified field
`ClassFormation.DegreeData.maximalUnramifiedField` (M029.016, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`); the infinite norm subgroup
`ClassFormation.infiniteNormSubgroup A E K` (M029.004), the infimum over the
finite intermediate fields `M : FiniteIntermediateField E K` (M029.001) of
the norm ranges `finiteIntermediateNormRange A E K M` (M029.003), and
`ClassFormation.DegreeData.maximalUnramifiedNormSubgroup D A K L` (M029.024),
defined as `infiniteNormSubgroup A (D.maximalUnramifiedField L) K`, both in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions`; and, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Main.Definitions`, the quotient
`ClassFormation.InfiniteNormQuotient A E K` (M029.006), its lift
`ClassFormation.infiniteNormQuotientLift A E K f hf` (M029.014), the quotient
`ClassFormation.DegreeData.MaximalUnramifiedNormQuotient D A K L` (M029.027),
defined as `InfiniteNormQuotient A (D.maximalUnramifiedField L) K`, its
additive group instance (M029.028) and the class map
`ClassFormation.DegreeData.maximalUnramifiedNormClass` (M029.030). The
coefficient module `KummerTheory.ambientFixedAddSubgroup A K` (M023.001) of
the elements of `A` fixed by `K` is found through `open KummerTheory`.
Mathlib supplies `Rep`, `ClosedSubgroup`, `AddMonoidHom` with its kernel,
`AddSubgroup` and `Iff.rfl`.

The last line of the source body applies M029.026
`mem_maximalUnramifiedNormSubgroup_iff`, whose statement is published but
whose proof is not. Its source (lines 306–313) is

```lean
/-- Membership in the maximal unramified norm subgroup is characterized levelwise. -/
@[simp]
theorem mem_maximalUnramifiedNormSubgroup_iff
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    a ∈ D.maximalUnramifiedNormSubgroup A K L ↔
      a ∈ infiniteNormSubgroup A (D.maximalUnramifiedField L) K := by
  rw [D.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup]
```

and the theorem it rewrites with, M029.025, is proved by `rfl` (lines
298–304):

```lean
/-- The maximal-unramified norm subgroup is the infinite norm subgroup for
the maximal unramified field. -/
theorem maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    D.maximalUnramifiedNormSubgroup A K L =
      infiniteNormSubgroup A (D.maximalUnramifiedField L) K := by
  rfl
```

The port writes the same equivalence in place, stated with `show` and proved
by `Iff.rfl`: the two memberships agree by unfolding the definition of
`maximalUnramifiedNormSubgroup`.

## Definition

The definition has the section binders implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`, where `IntegralRepGroupType` is the
universe-zero type of acting groups that Mathlib's `Rep ℤ G` requires,
followed by the binders shown.

```lean
/-- Descend an additive homomorphism that kills the maximal-unramified norm subgroup. -/
def maximalUnramifiedNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : D.maximalUnramifiedNormSubgroup A K L ≤ f.ker) :
    D.MaximalUnramifiedNormQuotient A K L →+ B := by
  unfold MaximalUnramifiedNormQuotient
  refine infiniteNormQuotientLift A (D.maximalUnramifiedField L) K f ?_
  intro a ha
  exact hf ((show a ∈ D.maximalUnramifiedNormSubgroup A K L ↔
      a ∈ infiniteNormSubgroup A (D.maximalUnramifiedField L) K from
    Iff.rfl).2 ha)
```

For an additive group `B` and an additive homomorphism
`f : A_K →+ B` whose kernel contains the maximal-unramified norm subgroup
`N_{\widetilde L|K} A_{\widetilde L}` (`hf`), the definition is the induced
homomorphism `A_K / N_{\widetilde L|K} A_{\widetilde L} →+ B`: after
unfolding `MaximalUnramifiedNormQuotient` it is
`infiniteNormQuotientLift A (D.maximalUnramifiedField L) K f`, whose
hypothesis (that `f` kills the infinite norm subgroup) follows from `hf`.
Only the proof term of that hypothesis differs from the source, and by proof
irrelevance the definition is the source one.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift`.
2. Replace `(D.mem_maximalUnramifiedNormSubgroup_iff A K L a).2 ha` in the
   last line by `(show a ∈ D.maximalUnramifiedNormSubgroup A K L ↔ a ∈
   infiniteNormSubgroup A (D.maximalUnramifiedField L) K from Iff.rfl).2 ha`,
   written over three lines, as explained above.
3. Copy the docstring, the binders and the other body lines verbatim; a line
   diff against the pinned source shows no other difference.
4. Replace the two source imports by the published module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Main.Definitions`, and the source module docstring by
   a description of this module with a modification notice.
5. Keep the source context listed above, without `universe u`; omit the
   other declarations of the source file. No helper declaration, instance or
   linter option is added.

This is a definition only. It discharges no host class-formation, Tate or
reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), together with the other three
modules of this contribution, with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
