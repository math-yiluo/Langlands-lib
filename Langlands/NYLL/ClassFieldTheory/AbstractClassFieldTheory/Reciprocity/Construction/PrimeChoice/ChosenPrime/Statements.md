# NYLL M030.002, M030.003, M030.005: targets that the chosen prime element is a prime element

The paired Lean file adapts the statements of three theorems of Naganori
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

| Unit | Source theorem after `ClassFormation.ValuationData.` | Docstring | Attribute | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.ValuationData.` |
| --- | --- | --- | --- | --- | --- | --- |
| M030.002 | `valuationAt_chosenPrimeElement` | 39 | 40 | 41–43 | 44 | `valuationAt_chosenPrimeElementStatement` |
| M030.003 | `chosenPrimeElement_isPrime` | 46 | — | 47–49 | 50 | `chosenPrimeElement_isPrimeStatement` |
| M030.005 | `sub_chosenPrimeElement_mem_unitAddSubgroup` | 61 | — | 62–66 | 67–68 | `sub_chosenPrimeElement_mem_unitAddSubgroupStatement` |

The source file imports
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements`
(line 7). Its context is `namespace ClassFormation` (line 17),
`open KummerTheory` (line 19), `open CyclicCohomology` (line 21),
`noncomputable section` (line 25), `namespace ValuationData` (lines 27 and
70), the comment and variable lines 29–31, which in this source file follow
`namespace ValuationData`,

```lean
-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}
```

and the closing lines 72–73. The port keeps this context verbatim and in
the same order. The declarations have the section binders implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}`, followed
by the binders shown. The group lies in `Type 0`; the carrier of `A` has an
arbitrary universe, the single universe parameter. Each target is a `Prop`.

The statements use the chosen prime element
`ValuationData.chosenPrimeElement v K` (M030.001), ported in the companion
module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.Definitions`
of this contribution. The other names resolve to published
`Langlands.NYLL.ClassFormation` declarations: the normalized valuation
`ValuationData.valuationAt` (M025.025, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`), the
distinguished value `ValuationData.oneValue` (M028.005, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.Definitions`), the prime-element
predicate `ValuationData.IsPrimeElement v K π`, that is,
`v.valuationAt K π = v.oneValue` (M028.007), and the additive unit group
`ValuationData.unitAddSubgroup v K`, the kernel of the normalized valuation
(M028.008), both in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions`;
`ValuationData` (M025.012); `FiniteAbstractField` (M010.121); `DegreeData`
(M010.002); `KummerTheory.ambientFixedAddSubgroup` (M023.001, through
`open KummerTheory`); and `IntegralRepGroupType` (M002.001). Subtraction in
the additive subgroup `ambientFixedAddSubgroup A K.field`, membership in an
`AddSubgroup` and `Rep` are Mathlib's.

## Targets and complete telescopes

### M030.002

```lean
/-- The proposition, from the source theorem `valuationAt_chosenPrimeElement`,
that `v.valuationAt K (v.chosenPrimeElement K) = v.oneValue`. -/
def valuationAt_chosenPrimeElementStatement (v : ValuationData D A)
    (K : FiniteAbstractField G) : Prop :=
    v.valuationAt K (v.chosenPrimeElement K) = v.oneValue
```

The chosen prime element has normalized valuation `v.oneValue`.

### M030.003

```lean
/-- The proposition, from the source theorem `chosenPrimeElement_isPrime`,
that the chosen prime element is a prime element: its valuation is the
distinguished degree-one value. -/
def chosenPrimeElement_isPrimeStatement (v : ValuationData D A)
    (K : FiniteAbstractField G) : Prop :=
    v.IsPrimeElement K (v.chosenPrimeElement K)
```

The chosen prime element is a prime element of `K`. As a proposition this
unfolds to the target M030.002; the source proves it by M030.002.

### M030.005

```lean
set_option linter.unusedVariables false in
/-- The proposition, from the source theorem
`sub_chosenPrimeElement_mem_unitAddSubgroup`, that for a prime element `π`,
`π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K`. -/
def sub_chosenPrimeElement_mem_unitAddSubgroupStatement
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) : Prop :=
    π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K
```

For every prime element `π` of `K`, the difference
`π - v.chosenPrimeElement K` lies in the additive unit group `U_K`. The
implicit `π` and the explicit hypothesis `hπ` have the source names, order
and kinds. The proposition does not mention `hπ`, exactly as in the source,
where it is used only by the proof; a prover of the target receives it as a
hypothesis. The companion target M030.004
`sub_mem_unitAddSubgroup_of_primeStatement`, used by the source proof, is
already published in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.PrimeDifference.Statements`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ClassFormation.ValuationData`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order; `: Prop :=` is appended to the last telescope line. The source
   proofs are omitted: this contribution publishes the proposition targets,
   and their proofs are separate work.
3. Omit the `@[simp]` attribute of M030.002: a definition of a proposition
   is not a simp lemma.
4. Precede M030.005 by `set_option linter.unusedVariables false in`.
   Without it, Lean's unused-variables linter warns about `hπ`, which the
   proposition does not mention. The option affects only the linter and
   keeps the source binder name; it changes no term.
5. Replace each source docstring by a description of the proposition that
   names the source theorem, and the source module docstring by a
   description of this module with a modification notice.
6. Replace the source import by the companion module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.Definitions`
   and the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions`,
   which import the modules of all names listed above.
7. Keep the source context listed above; omit M030.001 (ported in the
   companion module), M030.004 (published) and the proofs. No helper
   declaration or instance is added.

These are exact source statements as named propositions, without published
proofs. They discharge no host class-formation, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), together with the other five
modules of this contribution, with no errors or warnings. Declaration inspection of M030.005 reported a `Prop` target, one universe parameter and the axioms `propext`, `Classical.choice` and `Quot.sound`.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
