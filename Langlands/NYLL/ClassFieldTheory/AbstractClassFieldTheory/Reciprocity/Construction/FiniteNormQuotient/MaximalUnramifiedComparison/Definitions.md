# NYLL M039.021: the comparison map from the maximal-unramified to a finite norm quotient

The paired Lean file adapts one definition of Naganori
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

| Unit | Source definition after `ClassFormation.DegreeData.` | Docstring | Header | Body | Adapted name after `Langlands.NYLL.ClassFormation.DegreeData.` |
| --- | --- | --- | --- | --- | --- |
| M039.021 | `maximalUnramifiedToFiniteNormQuotient` | 277–278 | 279–284 | 285–287 | `maximalUnramifiedToFiniteNormQuotient` |

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

The names used resolve to published `Langlands.NYLL` declarations: the lift
`ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift` (M029.035) in
the companion module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.QuotientLift.Definitions` of this
contribution, which imports the maximal-unramified quotient
`MaximalUnramifiedNormQuotient` (M029.027) and
`maximalUnramifiedNormSubgroup` (M029.024) as described in its Markdown;
in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`: the finite norm subgroup
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
(M004.002); the definition
`ClassFormation.DegreeData.fieldAsMaximalUnramifiedIntermediate` (M039.018,
`L` as a finite intermediate field of `\widetilde L | K`) in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramifiedIntermediate.Definitions`, from the
accepted candidate `92547b75-a5da-42fd-824a-141ead58e124` (independent
review accepted; Library integration pending), which this contribution
therefore requires first; and `infiniteNormSubgroup` (M029.004) with its
norm ranges `finiteIntermediateNormRange` (M029.003). Mathlib supplies
`QuotientAddGroup.eq_zero_iff`, `iInf_le_of_le` and the kernel of an
additive homomorphism.

The source body passes the private source theorem M039.020
`maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker` (lines 267–275),
whose statement is published as
`Langlands.NYLL.PortInternal.M039.d020Statement` but whose proof is not:

```lean
private theorem maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    D.maximalUnramifiedNormSubgroup A K L ≤
      (finiteNormClassHom A K L hLK).ker := by
  intro a ha
  exact (finiteNormClass_eq_zero_iff A K L hLK a).2
    (D.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup A K L hLK ha)
```

It applies M039.012 `finiteNormClass_eq_zero_iff` (lines 147–157) and
M039.019 `maximalUnramifiedNormSubgroup_le_finiteNormSubgroup` (lines
254–265), whose statements are published but whose proofs are not either:

```lean
/-- A finite norm class vanishes exactly when its representative lies in the norm subgroup. -/
@[simp]
theorem finiteNormClass_eq_zero_iff
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK a = 0 ↔
      a ∈ finiteNormSubgroup A K L hLK := by
  unfold finiteNormClass finiteNormClassHom FiniteNormQuotient
  exact QuotientAddGroup.eq_zero_iff _
```

```lean
/-- The defining intersection for the infinite norm subgroup is contained
in the norm image from the particular finite field `L`. -/
theorem maximalUnramifiedNormSubgroup_le_finiteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    D.maximalUnramifiedNormSubgroup A K L ≤
      finiteNormSubgroup A K L hLK := by
  rw [D.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup]
  rw [infiniteNormSubgroup]
  refine iInf_le_of_le (D.fieldAsMaximalUnramifiedIntermediate K L hLK) ?_
  rfl
```

The first rewrite of the M039.019 proof uses the `rfl` theorem M029.025
`maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup` of `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
(lines 298–304). The port writes the source proof of M039.020 in place of
the theorem, as a `by` block: after `intro a ha`, it states the local facts
`hzero` (the statement of M039.012 at `a`, proved by its source proof:
`unfold finiteNormClass finiteNormClassHom FiniteNormQuotient` and
`QuotientAddGroup.eq_zero_iff`) and `hle` (the statement of M039.019, proved
by its source proof with the rewrite by M029.025 replaced by `show` of the
rewritten goal, since the two sides agree by definition; then
`rw [infiniteNormSubgroup]`, `iInf_le_of_le` at
`D.fieldAsMaximalUnramifiedIntermediate K L hLK` and `rfl`), and concludes
with `hzero.2 (hle ha)`, the last line of the M039.020 proof.

## Definition

The definition has the section binders implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`, where `IntegralRepGroupType` is the
universe-zero type of acting groups that Mathlib's `Rep ℤ G` requires,
followed by the binders shown.

```lean
/-- The canonical quotient map
`A_K/N_{\widetilde L|K}A_{\widetilde L} → A_K/N_{L|K}A_L`. -/
def maximalUnramifiedToFiniteNormQuotient
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    D.MaximalUnramifiedNormQuotient A K L →+
      FiniteNormQuotient A K L hLK :=
  D.maximalUnramifiedNormQuotientLift A K L
    (finiteNormClassHom A K L hLK)
    (by
      intro a ha
      have hzero : finiteNormClass A K L hLK a = 0 ↔
          a ∈ finiteNormSubgroup A K L hLK := by
        unfold finiteNormClass finiteNormClassHom FiniteNormQuotient
        exact QuotientAddGroup.eq_zero_iff _
      have hle : D.maximalUnramifiedNormSubgroup A K L ≤
          finiteNormSubgroup A K L hLK := by
        show infiniteNormSubgroup A (D.maximalUnramifiedField L) K ≤
          finiteNormSubgroup A K L hLK
        rw [infiniteNormSubgroup]
        refine iInf_le_of_le (D.fieldAsMaximalUnramifiedIntermediate K L hLK) ?_
        rfl
      exact hzero.2 (hle ha))
```

For closed subgroups `K` and `L` with `G_L ≤ G_K` of finite index, the
definition is the canonical map
`A_K / N_{\widetilde L|K} A_{\widetilde L} →+ A_K / N_{L|K} A_L`: the lift of
the finite quotient map `finiteNormClassHom A K L hLK`, which kills the
maximal-unramified norm subgroup because that subgroup, an intersection of
norm ranges over the finite intermediate fields of `\widetilde L | K`, lies in
the norm range from `L` itself. Only the proof argument differs from the
source term, and by proof irrelevance the definition is the source one.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient`.
2. Replace the finiteness binder
   `[hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]` by
   `[hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`,
   its exact body, as the published finite norm quotient and the published
   statements of M039.019 and M039.020 do.
3. Replace the argument
   `(D.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker A K L hLK)` by
   the `by` block described above.
4. Copy the docstring, the other binders and the rest of the body verbatim;
   a line diff against the pinned source shows no other difference.
5. Replace the two source imports by the companion module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.QuotientLift.Definitions`, the published module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions` and the module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramifiedIntermediate.Definitions`, and
   the source module docstring by a description of this module with a
   modification notice.
6. Keep the source context listed above, without `universe u` and
   `open CyclicCohomology`; omit the other declarations of the source file.
   No helper declaration, instance or linter option is added.

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
