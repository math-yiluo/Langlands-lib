# NYLL M039.022: the comparison map on maximal-unramified norm classes (target)

The paired Lean file adapts the statement of one theorem of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`.
The pinned source file has SHA-256
`f541cbe9d1f0a01b867d7339fc7ef0eb830bd9bf799ceaadfb6506c4bb334da7`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Statement | Proof (omitted) | Target after `Langlands.NYLL.ClassFormation.DegreeData.` |
| --- | --- | --- | --- | --- | --- |
| M039.022 | `maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass` | 289–290 | 292–299 (attribute `@[simp]` line 291) | 300–302 | `maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClassStatement` |

The source file imports
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup`
and `Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` (lines 7–8). The
context is `universe u` (line 18), `namespace ClassFormation` (line 20),
`open KummerTheory` (line 22), `open CyclicCohomology` (line 24),
`noncomputable section` (line 28), the section `quotientMaps` (lines 247 and
306) with the comment and variable lines 249–250,

```lean
-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
```

`namespace DegreeData` (lines 252 and 304) and the closing lines 308–309.
The port keeps this context in the same order and omits `universe u` and
`open CyclicCohomology`, which the section does not use.

The source theorem is

```lean
/-- The comparison to a finite norm quotient carries the maximal-unramified
class to its finite-level class. -/
@[simp]
theorem maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedToFiniteNormQuotient A K L hLK
        (D.maximalUnramifiedNormClass A K L a) =
      finiteNormClass A K L hLK a := by
  exact D.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass
    A K L (finiteNormClassHom A K L hLK)
    (D.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker A K L hLK) a
```

The names used resolve to `Langlands.NYLL` declarations: the comparison map
`ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient` (M039.021)
in the companion module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramifiedComparison.Definitions` of this
contribution, which imports the published class map
`ClassFormation.DegreeData.maximalUnramifiedNormClass` (M029.030, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Main.Definitions`) and, in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`: the finite norm subgroup
`ClassFormation.finiteNormSubgroup A K L hLK` (M039.001), the range of the
relative norm from `A_L` to `A_K`, the quotient
`ClassFormation.FiniteNormQuotient A K L hLK` (M039.002) with its additive
group instance (M039.003), the quotient map
`ClassFormation.finiteNormClassHom A K L hLK` (M039.005, the map
`QuotientAddGroup.mk'` after unfolding) and the class
`ClassFormation.finiteNormClass A K L hLK a` (M039.006, defined as
`finiteNormClassHom A K L hLK a`). These published definitions take the
finiteness instance in the form
`[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`, the exact
`Subgroup.subgroupOf` body of the source's `extensionSubgroup K L hLK`
(M004.002). The coefficient
module `KummerTheory.ambientFixedAddSubgroup A K` (M023.001) is found
through `open KummerTheory`.

## Target

The target has the section binders implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`, followed by the binders shown.

```lean
/-- The proposition, from the source theorem
`maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass`, that the
comparison to a finite norm quotient carries the maximal-unramified class of
`a` to its finite-level class. -/
def maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClassStatement
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A K) : Prop :=
    D.maximalUnramifiedToFiniteNormQuotient A K L hLK
        (D.maximalUnramifiedNormClass A K L a) =
      finiteNormClass A K L hLK a
```

For closed subgroups `K` and `L` with `G_L ≤ G_K` of finite index and
`a ∈ A_K`, the proposition says that the comparison map sends the
maximal-unramified norm class of `a` to its finite norm class modulo
`N_{L|K} A_L`. The binders, except for the form of the finiteness binder, and
the proposition are the source theorem's.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL` and replace the source theorem
   by the Prop-valued definition
   `Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClassStatement`
   whose body is the source proposition; the source proof (lines 300–302)
   and the `@[simp]` attribute are omitted.
2. Replace the finiteness binder
   `[hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]` by
   `[hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`,
   its exact body, as the published finite norm quotient does.
3. Reword the docstring to describe the proposition.
4. Replace the source imports by the companion module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramifiedComparison.Definitions`, and the
   source module docstring by a description of this module with a
   modification notice.
5. Keep the source context listed above, without `universe u` and
   `open CyclicCohomology`; omit the other declarations of the source file.
   No helper declaration, instance or linter option is added.

This is a target statement only; its proof is not part of this module. It
discharges no host class-formation, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), together with the other three
modules of this contribution, with no errors or warnings. The inspection of the target reported a Prop-valued definition with one universe parameter `u_1` and only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
