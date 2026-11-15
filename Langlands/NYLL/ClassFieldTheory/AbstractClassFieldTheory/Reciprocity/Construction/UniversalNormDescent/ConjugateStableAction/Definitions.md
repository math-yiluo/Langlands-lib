# NYLL M043.003: the conjugation-stable action on fixed elements

The paired Lean file adapts one definition of Naganori
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

| Unit | Source definition after `ClassFormation.` | Docstring | Definition | Adapted name after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- |
| M043.003 | `conjugateStableAction` | 71–72 | 73–78 | `conjugateStableAction` |

The source context is `universe u v` (line 18),
`namespace ClassFormation` (line 20), `open KummerTheory` (line 22),
`open CyclicCohomology` (line 23), `noncomputable section` (line 27),
`open CategoryTheory` (line 29) and `open scoped BigOperators` (line 30);
there is no variable declaration. The source imports are the NYLL module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CoreFrobeniusNorm`
and `Mathlib.Dynamics.BirkhoffSum.Basic` (lines 7–8). The other
declarations of the source file are outside this contribution.

The definition uses these published declarations:

- `conjugateFixedElement A K σ a` (M026.003, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions`), the element
  `A.ρ σ⁻¹ a.1` of `ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)`,
  the right conjugate `a^σ` of `a : A_K`;
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

The module imports `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions`,
contributed together with this module, which imports the other
declarations above.

## Definition and complete telescope

The telescope shown is complete.

```lean
noncomputable def conjugateStableAction
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) : ambientFixedAddSubgroup B F :=
  hF ▸ conjugateFixedElement B F s a
```

For a closed subgroup `F` with `conjugateClosedSubgroup F s = F` (the field
`F` is stable under conjugation by `s`), this sends `a : B_F` to the right
conjugate `conjugateFixedElement B F s a : B_{F^s}`, transported back to
`B_F` along `hF`. Its underlying element is `B.ρ s⁻¹ a.1` (M043.006).

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.ClassFormation.conjugateStableAction`.
2. Copy the docstring, the binders and the body verbatim.
3. Replace the source imports by the focused import above and the source
   module docstring by a description of this module with a modification
   notice.
4. Keep `universe u v`, the namespace, the opens, the noncomputable
   section, `open CategoryTheory` and `open scoped BigOperators`; omit the
   rest of the source file.
5. No helper declaration, instance or linter option is added.

It discharges no host class-formation, cup, transfer, Tate or reciprocity
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
