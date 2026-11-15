# NYLL M026.004: the coercion of the right conjugate of a fixed element

The paired Lean file adapts the statement of one theorem of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`.
The pinned source file has SHA-256
`985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.` | Docstring | Attribute | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- | --- | --- |
| M026.004 | `conjugateFixedElement_coe` | 79–82 | 83 | 84–89 | 89–90 | `conjugateFixedElement_coeStatement` |

The source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (line 18), `open CyclicCohomology` (line 20),
`noncomputable section` (line 24), `open scoped BigOperators Pointwise`
(line 26) and the variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 29, after
the comment line 28). The source imports are the NYLL modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation` and
`Nyll.GaloisCohomology.GroupTheory.QuotientTower` (lines 7–8). The other
declarations of the source file are outside this contribution.

The statement uses these declarations:

- `conjugateFixedElement A K σ a` (M026.003, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions`, contributed
  together with this module), the right conjugate `A.ρ σ⁻¹ a.1` of `a`;
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
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions`.

## Target and complete telescope

The target has, before the binders shown, the binders of the source
variable line 29: implicit `{G : IntegralRepGroupType}` and the instances `[Group G]` and
`[TopologicalSpace G]`.

```lean
def conjugateFixedElement_coeStatement [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K) : Prop :=
    ((conjugateFixedElement A K σ a :
      ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)) : A.V) =
      A.ρ σ⁻¹ a.1
```

The underlying element of `A.V` of the right conjugate
`conjugateFixedElement A K σ a` is `A.ρ σ⁻¹ a.1`. The source proof is `rfl`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the target lies in
   `Langlands.NYLL.ClassFormation`.
2. Replace `theorem conjugateFixedElement_coe … : statement := rfl` by
   `def conjugateFixedElement_coeStatement … : Prop := statement`. The
   telescope and the statement are copied verbatim, including the binder
   names, kinds and order and the line breaks. The proof `rfl` and the
   `@[simp]` attribute, which does not apply to a definition of a
   proposition, are omitted; the proof is separate work.
3. Prefix the source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged, and the lines are
   rewrapped. Replace the source module docstring by a description of this
   module with a modification notice.
4. Replace the source imports by the focused import above.
5. Keep the namespace, both opens, the noncomputable section,
   `open scoped BigOperators Pointwise`, the comment line 28 and the variable
   line 29; omit the rest of the source file.
6. No helper declaration, instance or linter option is added.

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
