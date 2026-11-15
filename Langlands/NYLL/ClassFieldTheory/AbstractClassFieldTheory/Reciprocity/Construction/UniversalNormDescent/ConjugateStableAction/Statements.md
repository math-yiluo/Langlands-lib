# NYLL M043.006 and M043.007: the conjugation-stable action and its compatibility with norms

The paired Lean file adapts the statements of two theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`.
The pinned source file has SHA-256
`5ac5450e039760193ab008f2bed81158a543d2d9982515cd2e376baeadfe1284`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.` | Docstring | Attribute | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- | --- | --- |
| M043.006 | `conjugateStableAction_coe` | 104 | 105 | 106–112 | 112–113 | `conjugateStableAction_coeStatement` |
| M043.007 | `relativeNorm_conjugateStableAction` | 115–116 | none | 117–126 | 126–149 | `relativeNorm_conjugateStableActionStatement` |

The source context is `universe u v` (line 18),
`namespace ClassFormation` (line 20), `open KummerTheory` (line 22),
`open CyclicCohomology` (line 23), `noncomputable section` (line 27),
`open CategoryTheory` (line 29) and `open scoped BigOperators` (line 30);
there is no variable declaration. The source imports are the NYLL module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CoreFrobeniusNorm`
and `Mathlib.Dynamics.BirkhoffSum.Basic` (lines 7–8). The other
declarations of the source file are outside this contribution.

The statements use these declarations:

- `conjugateStableAction B F s hF a` (M043.003, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.Definitions`,
  contributed together with this module), the right conjugate of `a : B_F`
  by `s`, transported back to `B_F` along `hF : conjugateClosedSubgroup F s = F`;
- `relativeNorm A K L hLK` (M024.009, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`), for `hLK : G_L ≤ G_K` and
  finite `G_K ⧸ G_L`, the additive homomorphism
  `ambientFixedAddSubgroup A L →+ ambientFixedAddSubgroup A K` given by the
  sum of `A.ρ k a` over representatives `k` of the cosets of `G_L` in
  `G_K`;
- `CyclicCohomology.extensionSubgroup K L hLK` (M004.002, from
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  available through `open CyclicCohomology`), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`, that is `G_L` as a subgroup of
  `G_K`;
- `IntegralRepGroupType` (M002.001, from
  `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse`), the
  abbreviation `Type 0`, used because Mathlib's `Rep ℤ G` fixes the acting
  group to universe zero;
- `KummerTheory.ambientFixedAddSubgroup A H` (M023.001, from
  `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`,
  available through `open KummerTheory`), the additive subgroup
  `{a | ∀ h : H.toSubgroup, A.ρ h.1 a = a}` of `A.V`, the elements of the
  representation `A : Rep ℤ G` fixed by the closed subgroup `H`, that is
  `A_H`;
- `conjugateClosedSubgroup K σ` (M026.001, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`), the closed subgroup of `G` whose
  underlying subgroup is `ConjAct.toConjAct σ⁻¹ • K.toSubgroup`, that is
  `σ⁻¹ G_K σ`, the subgroup of the right conjugate field `K^σ`;
- Mathlib's `ClosedSubgroup G`, with its underlying subgroup
  `K.toSubgroup`, and Mathlib's `Rep ℤ G`, with the underlying group `A.V`
  and the action `A.ρ`.

The module imports
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.Definitions`
and `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`.

## Targets and complete telescopes

The telescopes shown are complete.

```lean
def conjugateStableAction_coeStatement
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) : Prop :=
    ((conjugateStableAction B F s hF a : ambientFixedAddSubgroup B F) : B.V) =
      B.ρ s⁻¹ a.1
```

M043.006: the underlying element of `conjugateStableAction B F s hF a` is
`B.ρ s⁻¹ a.1`.

```lean
def relativeNorm_conjugateStableActionStatement
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F E : ClosedSubgroup R)
    (hEF : E.toSubgroup ≤ F.toSubgroup) (s : R)
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (hF : conjugateClosedSubgroup F s = F)
    (hE : conjugateClosedSubgroup E s = E)
    (a : ambientFixedAddSubgroup B E) : Prop :=
    relativeNorm B F E hEF (conjugateStableAction B E s hE a) =
      conjugateStableAction B F s hF (relativeNorm B F E hEF a)
```

M043.007: for closed subgroups `E ≤ F` with finite `G_F ⧸ G_E`, both stable
under conjugation by `s`, the relative norm from `B_E` to `B_F` commutes with
the conjugation-stable actions of `s` on `B_E` and `B_F`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ClassFormation`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order and the line breaks. The proofs and the `@[simp]` attribute of
   M043.006, which does not apply to a definition of a proposition, are
   omitted; the proofs are separate work.
3. Prefix the source docstrings with `Target:` and lower-case the first
   word after it; the wording is otherwise unchanged and the lines are
   rewrapped. Replace the source module docstring by a description of this
   module with a modification notice.
4. Replace the source imports by the two focused imports above.
5. Keep `universe u v`, the namespace, the opens, the noncomputable
   section, `open CategoryTheory` and `open scoped BigOperators`; omit the
   rest of the source file.
6. No helper declaration, instance or linter option is added: every
   hypothesis is mentioned by its proposition. The private source theorems
   `transport_fixed_coe` and `relativeNorm_transport_coe` (lines 80–102),
   used only by the source proofs, are not part of this module.

This is the exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer, Tate or reciprocity
target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
