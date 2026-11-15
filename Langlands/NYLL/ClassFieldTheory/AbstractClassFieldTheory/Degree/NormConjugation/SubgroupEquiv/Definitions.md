# NYLL M035.002: conjugation of a field subgroup onto its right conjugate

The paired Lean file adapts one definition of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean`.
The pinned source file has SHA-256
`2ec220a4a18e54914548db7f0ecea669819fe5b6f8b421c13e996dd6ceed4602`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.` | Docstring | Definition | Adapted name after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- |
| M035.002 | `conjugateSubgroupEquiv` | 48–49 | 50–68 | `conjugateSubgroupEquiv` |

The source context is `namespace ClassFormation` (line 18),
`open KummerTheory` (line 20), `open CyclicCohomology` (line 22),
`noncomputable section` (line 26), `open scoped BigOperators` (line 28),
`universe u` (line 30), `section GroupOnly` (line 32) and the variables
`{G : Type u} [Group G] [TopologicalSpace G]` (line 34). The source imports
are the NYLL modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws` and
`Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` (lines 7–8). The other
declarations of the source file are outside this contribution.

The definition uses these published declarations:

- `conjugateClosedSubgroup K σ` (M026.001, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`), the closed subgroup of `G` whose
  underlying subgroup is `ConjAct.toConjAct σ⁻¹ • K.toSubgroup`, that is
  `σ⁻¹ G_K σ`, the subgroup of the right conjugate field `K^σ`;
- `conjugateClosedSubgroup_mem` (M026.002, proved in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs`), whose type is
  `conjugateClosedSubgroup_memStatement K σ x` (from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements`), the proposition
  `x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K`;
- Mathlib's `ClosedSubgroup G`, with its underlying subgroup
  `K.toSubgroup` and the subspace topology on `K.toSubgroup`.

The module imports `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs`, which imports the
definitions and statements above.

## Definition and complete telescope

The definition has, before the binders shown, the binders of the source
variable line 34: implicit `{G : Type u}` and the instances `[Group G]` and
`[TopologicalSpace G]`.

```lean
def conjugateSubgroupEquiv [ContinuousMul G]
    (K : ClosedSubgroup G) (s : G) :
    K.toSubgroup ≃* (conjugateClosedSubgroup K s).toSubgroup where
  toFun k := ⟨s⁻¹ * k.1 * s, by
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup K s
    refine (conjugateClosedSubgroup_mem K s _).2 ?_
    convert k.2 using 1
    simp [mul_assoc]⟩
  invFun x := ⟨s * x.1 * s⁻¹,
    (conjugateClosedSubgroup_mem K s x.1).mp x.2⟩
  left_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]
```

For a closed subgroup `K` of `G` and `s : G`, this is the multiplicative
equivalence `G_K ≃* G_{K^s} = s⁻¹ G_K s` sending `k` to `s⁻¹ * k * s`, with
inverse `x ↦ s * x * s⁻¹`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.ClassFormation.conjugateSubgroupEquiv`.
2. Copy the docstring, the binders and the data (`toFun`, `invFun`) and the
   proof fields verbatim except for one tactic: in the membership proof of
   `toFun`, `rw [conjugateClosedSubgroup_mem]` becomes
   `refine (conjugateClosedSubgroup_mem K s _).2 ?_`. The published theorem
   has the type `conjugateClosedSubgroup_memStatement K s x`, which `rw`
   does not unfold, while `.2` applies the reverse direction of the same
   equivalence. The change is inside a proof of a proposition, so the
   equivalence and its maps are those of the source.
3. Replace the source imports by the focused published import above and the
   source module docstring by a description of this module with a
   modification notice.
4. Keep the namespace, the noncomputable section, `universe u`, the section
   `GroupOnly` and the variable line 34; omit the opens, which the
   definition does not use, and the rest of the source file.
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
