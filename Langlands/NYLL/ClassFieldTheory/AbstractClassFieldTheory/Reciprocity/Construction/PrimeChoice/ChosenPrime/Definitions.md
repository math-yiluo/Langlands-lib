# NYLL M030.001: the chosen prime element of a finite abstract field

The paired Lean file adapts one definition of Naganori
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

The definition also contains the source proof of the theorem M025.027
`ClassFormation.ValuationData.normalizedValuation_surjective` from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`, SHA-256
`f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c`, in the same snapshot.

## Source correspondence

| Unit | Source definition after `ClassFormation.ValuationData.` | Docstring | Header | Body | Adapted name after `Langlands.NYLL.ClassFormation.ValuationData.` |
| --- | --- | --- | --- | --- | --- |
| M030.001 | `chosenPrimeElement` | 33–34 | 35–36 | 37 | `chosenPrimeElement` |

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
arbitrary universe, the single universe parameter.

The source body is

```lean
  Classical.choose (v.normalizedValuation_surjective K v.oneValue)
```

It applies the theorem M025.027 `normalizedValuation_surjective`
(`Valuation.lean`, lines 299–323), stating
`Function.Surjective (v.valuationAt K)`, to the distinguished value
`v.oneValue`. That theorem has no published proof. The port replaces
`v.normalizedValuation_surjective K` by the term

```lean
(show Function.Surjective (v.valuationAt K) by
  …)
```

whose tactic block is the source proof of M025.027 (lines 304–323), with one
change: its line `rw [← v.normCompositeAt_range K] at hzImage` uses the
theorem M025.020 `normCompositeAt_range` (`Valuation.lean`, lines 228–231),
whose proof is not published either. The port states that equation,
`(v.normCompositeAt K).range = nsmulImage v.valueGroup (K.residueDegree D : ℕ)`,
as a local `hrange` proved by `v.norm_range K`, which is the source proof of
M025.020 (line 231, the structure field `norm_range` of `ValuationData`),
and rewrites with `rw [← hrange] at hzImage`. The other tactic lines are the
source's, with their indentation shifted. `Classical.choose` depends only on
the proposition `∃ a, v.valuationAt K a = v.oneValue` and not on its proof,
so the chosen element is the source one by proof irrelevance.

The names used resolve to published `Langlands.NYLL.ClassFormation`
declarations: `ValuationData` (M025.012) with its field `norm_range`, the
value group `ValuationData.valueGroup` (M025.013) and the composite norm
valuation `ValuationData.normCompositeAt` (M025.019), all in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Definitions`;
`ValuationData.normCompositeAtInResidueImage` (M025.021) and the normalized
valuation `ValuationData.valuationAt` (M025.025), both in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`; `nsmulImage`
(M025.004, in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.Definitions`); the distinguished
value `ValuationData.oneValue` (M028.005, in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.Definitions`); `FiniteAbstractField`
(M010.121) and its residue degree (M010.127); `zHatMulNat` (M009.002, in
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U002.Definitions`),
`zHatDivide` (M009.016, in
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Definitions`)
and the published theorem `zHatDivide_zHatMulNat` (M009.018, in
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U018.Proofs`),
whose type is the published target, the equation that dividing
`zHatMulNat n z` by `n` gives `z`, accepted by `exact` because the type
unfolds to that equation; `KummerTheory.ambientFixedAddSubgroup` (M023.001,
through `open KummerTheory`); `DegreeData` (M010.002); and
`IntegralRepGroupType` (M002.001). Mathlib and core supply
`Classical.choose`, `Function.Surjective`, `AddMonoidHom.range`,
`Subtype.ext` and `Rep`.

## Definition

```lean
/-- A chosen prime element of a finite abstract field.  Later independence
lemmas show that the reciprocity class does not depend on this choice. -/
def chosenPrimeElement (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field :=
  Classical.choose
    ((show Function.Surjective (v.valuationAt K) by
      intro z
      have hzImage : (K.residueDegree D : ℕ) • z.1 ∈
          nsmulImage v.valueGroup (K.residueDegree D : ℕ) :=
        ⟨z.1, z.2, rfl⟩
      have hrange : (v.normCompositeAt K).range =
          nsmulImage v.valueGroup (K.residueDegree D : ℕ) :=
        v.norm_range K
      rw [← hrange] at hzImage
      obtain ⟨a, ha⟩ := hzImage
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change zHatDivide (K.residueDegree D : ℕ)
          (K.residueDegree D).property
            (v.normCompositeAtInResidueImage K a) = z.1
      have hsub : v.normCompositeAtInResidueImage K a =
          ⟨zHatMulNat (K.residueDegree D : ℕ) z.1, ⟨z.1, rfl⟩⟩ := by
        apply Subtype.ext
        change v.normCompositeAt K a =
          zHatMulNat (K.residueDegree D : ℕ) z.1
        exact ha
      rw [hsub]
      exact zHatDivide_zHatMulNat (K.residueDegree D : ℕ)
        (K.residueDegree D).property z.1) v.oneValue)
```

For a valuation datum `v` and a finite abstract field `K`, the definition
chooses an element of `A_K = ambientFixedAddSubgroup A K.field` whose
normalized valuation is `v.oneValue`, that is, a prime element. It exists
because the normalized valuation `A_K → Z` is surjective: for `z` in the
value group, `f_K z` lies in the range of the composite norm valuation, and
dividing by the residue degree `f_K` gives `z`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.ClassFormation.ValuationData.chosenPrimeElement`.
2. Replace the proof argument `v.normalizedValuation_surjective K` by the
   `show … by` term carrying the source proof of M025.027, with the local
   `hrange` for M025.020, as explained above. The application to
   `v.oneValue` and `Classical.choose` are unchanged.
3. Copy the docstring and the binders verbatim; a line diff against the
   pinned source (`PrimeChoice.lean` lines 33–37 and `Valuation.lean` lines
   304–323) shows only the changes listed here.
4. Replace the source import by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.Definitions` and
   `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U018.Proofs`,
   which import the modules of all names listed above, and the source module
   docstring by a description of this module with a modification notice.
5. Keep the source context listed above; omit the theorems of the source
   file (M030.002–M030.005). No helper declaration, instance or linter
   option is added.

This is a definition only. It discharges no host class-formation, Tate or
reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), together with the other five
modules of this contribution, with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
