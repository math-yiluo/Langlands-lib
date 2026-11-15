# NYLL M035.001: conjugation preserves inclusions of abstract fields

The paired Lean file adapts the statement of one theorem of Naganori
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

| Unit | Source theorem after `ClassFormation.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- | --- |
| M035.001 | `conjugateClosedSubgroup_mono` | 36 | 37–41 | 41–46 | `conjugateClosedSubgroup_monoStatement` |

The source context is `namespace ClassFormation` (line 18),
`open KummerTheory` (line 20), `open CyclicCohomology` (line 22),
`noncomputable section` (line 26), `open scoped BigOperators` (line 28),
`universe u` (line 30), `section GroupOnly` (line 32) and the variables
`{G : Type u} [Group G] [TopologicalSpace G]` (line 34). The source imports
are the NYLL modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws` and
`Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` (lines 7–8). The other
declarations of the source file are outside this contribution.

The statement uses these published declarations:

- `conjugateClosedSubgroup K σ` (M026.001, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`), the closed subgroup of `G` whose
  underlying subgroup is `ConjAct.toConjAct σ⁻¹ • K.toSubgroup`, that is
  `σ⁻¹ G_K σ`, the subgroup of the right conjugate field `K^σ`;
- Mathlib's `ClosedSubgroup G`, with its underlying subgroup
  `K.toSubgroup` and the subspace topology on `K.toSubgroup`.

The module imports `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`.

## Target and complete telescope

The target has, before the binders shown, the binders of the source
variable line 34: implicit `{G : Type u}` and the instances `[Group G]` and
`[TopologicalSpace G]`.

```lean
def conjugateClosedSubgroup_monoStatement [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) : Prop :=
    (conjugateClosedSubgroup L s).toSubgroup ≤
      (conjugateClosedSubgroup K s).toSubgroup
```

For closed subgroups `K` and `L` of `G` with `G_L ≤ G_K` and `s : G`, the
subgroup `s⁻¹ G_L s` of the conjugate field `L^s` lies in the subgroup
`s⁻¹ G_K s` of `K^s`. The source hypothesis `hLK` is kept although the
proposition does not mention it: the statement asserts the inclusion under
that hypothesis, and the target has every source hypothesis in the source
binder order.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the target lies in
   `Langlands.NYLL.ClassFormation`.
2. Replace `theorem conjugateClosedSubgroup_mono … : statement := proof` by
   `def conjugateClosedSubgroup_monoStatement … : Prop := statement`. The
   telescope and the statement are copied verbatim, including the binder
   names, kinds and order and the line breaks. The source proof is omitted:
   this contribution publishes the proposition target, and its proof is
   separate work.
3. Prefix the source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged. Replace the source module
   docstring by a description of this module with a modification notice.
4. Replace the source imports by the focused published import above.
5. Keep the namespace, the noncomputable section, `universe u`, the section
   `GroupOnly` and the variable line 34; omit the opens, which the
   statement does not use, and the rest of the source file.
6. Precede the target by `set_option linter.unusedVariables false in`: its
   proposition does not mention the hypothesis `hLK`, which the linter
   reports as unused (a check without the option gave exactly this one
   warning). The option affects only that declaration.
7. No helper declaration or instance is added.

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
