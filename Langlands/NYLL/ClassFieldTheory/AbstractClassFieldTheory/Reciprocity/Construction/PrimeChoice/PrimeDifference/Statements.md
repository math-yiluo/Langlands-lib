# NYLL M030.004: two prime elements differ by a unit

The paired Lean file adapts the statement of one theorem from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean`.
The pinned source file has SHA-256
`e0990f82b6186844d73a340de97bcbc03ba4a270924f91b120841189c49b924d`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M030.004 | `ClassFormation.ValuationData.sub_mem_unitAddSubgroup_of_prime` | 52 | 53–57 | 58–59 | `Langlands.NYLL.ClassFormation.ValuationData.sub_mem_unitAddSubgroup_of_primeStatement` |

The enclosing source context is `namespace ClassFormation` (line 17),
`open KummerTheory` (line 19), `open CyclicCohomology` (line 21),
`noncomputable section` (line 25), `namespace ValuationData` (line 27) and
the comment and variables at lines 29–31, which in this source file follow
`namespace ValuationData`.

The names used in the statement resolve to published `Langlands.NYLL`
declarations: `ClassFormation.ValuationData.IsPrimeElement` (M028.007) and
`ClassFormation.ValuationData.unitAddSubgroup` (M028.008), both in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions`,
`ClassFormation.ValuationData` (M025.012),
`ClassFormation.FiniteAbstractField` (M010.121), `ClassFormation.DegreeData`
(M010.002), `KummerTheory.ambientFixedAddSubgroup` (M023.001) and
`IntegralRepGroupType` (M002.001). Subtraction in the additive subgroup
`ambientFixedAddSubgroup A K.field`, membership in an `AddSubgroup` and `Rep`
are Mathlib's.

## Target and complete telescope

The target has the section binders implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}`, followed by
the binders shown. The group lies in `Type 0`; the carrier of `A` has an
arbitrary universe, the single universe parameter.

```lean
set_option linter.unusedVariables false in
def sub_mem_unitAddSubgroup_of_primeStatement
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π π' : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) (hπ' : v.IsPrimeElement K π') : Prop :=
    π' - π ∈ v.unitAddSubgroup K
```

If `π` and `π'` in `A_K = ambientFixedAddSubgroup A K.field` are both prime
elements of `K` (normalized value `1`), then their difference `π' - π` lies
in the additive unit group `U_K`, the kernel of the normalized valuation. In
the multiplicative language of the source, two prime elements differ by a
unit.

Binder names, order and kinds are those of the source theorem: `π` and `π'`
are implicit, and the hypotheses `hπ` and `hπ'` are explicit. The
proposition does not mention the hypotheses, exactly as in the source, where
they are used only by the proof; a prover of the target receives them as
hypotheses.

## Modification record

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace `theorem sub_mem_unitAddSubgroup_of_prime … : statement := proof`
   by `def sub_mem_unitAddSubgroup_of_primeStatement … : Prop := statement`.
   The statement is copied verbatim. The source proof is omitted: this
   contribution publishes a proposition target, and its proof is separate
   work.
3. Precede the target by `set_option linter.unusedVariables false in`.
   Without it, Lean's unused-variables linter warns about `hπ` and `hπ'`,
   which the proposition does not mention. The option affects only the linter
   and keeps the source binder names; it changes no term.
4. Replace the source docstring by a description of the proposition that
   names the source theorem, and replace the source module docstring by a
   description of this module with a modification notice.
5. Replace the source import of `Degree.PrimeElements` by the focused import
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions`.
6. Retain both opens, the noncomputable section, `namespace ValuationData`,
   the group-variable comment and both variable lines in their source order.
   Omit all other source units, including M030.001 `chosenPrimeElement` and
   the theorems about it. No helper declaration or instance is added.

This is the exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer, Tate
or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Declaration inspection reported `statement_returns_prop: true`, one universe
parameter and the axioms `propext`, `Classical.choice` and `Quot.sound`.
Compilation and inspection are separate from independent semantic acceptance
and publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
