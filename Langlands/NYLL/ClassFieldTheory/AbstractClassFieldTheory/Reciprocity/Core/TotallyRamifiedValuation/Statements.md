# NYLL M075.029–M075.030: valuations along a finite totally ramified extension

The paired Lean file adapts the statements of the theorems `abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified` and `abstractReciprocity_totallyRamified_valuation_forces_exponent_zero` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean`.
The pinned source file has SHA-256
`0fc1bd5c66d628b74e079fd54af4a9df7334343e38186983257da5ce6a8f06fb`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M075.029 | `abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified` | 1178–1181 | 1182–1191 | 1191–1243 | `Langlands.NYLL.ClassFormation.abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamifiedStatement` |
| M075.030 | `abstractReciprocity_totallyRamified_valuation_forces_exponent_zero` | 1245–1247 | 1248–1259 | 1259–1266 | `Langlands.NYLL.ClassFormation.abstractReciprocity_totallyRamified_valuation_forces_exponent_zeroStatement` |

The enclosing source context is `namespace ClassFormation` (lines 24–1270),
`open KummerTheory` (line 26), `open CyclicCohomology` (line 28),
`noncomputable section` (lines 32–1269), `open CategoryTheory` (line 34),
the comment and variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and
`{D : DegreeData G} {A : Rep ℤ G}` (lines 36–38), and the nested
`noncomputable section` (lines 451–1268) with the comment and the variable
line `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (lines
453–454). Both theorems bind `D` and `A` themselves. The source imports
(lines 7–11) are the modules `ClassFieldAxiom`, `FieldRepresentation`,
`Construction.MainTransfer`, `CyclicNormQuotient` and
`FiniteGaloisSubextension` of
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity`. The rest of
the source file is not part of this module; the auxiliary `ZHat` step
M075.028 used by the source proof of M075.030 has its own published target
in `Reciprocity.Core.ZHat.Statements`.

The names used resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001, from
  `GaloisCohomology.Cyclic.IntegralRepUniverse`), the abbreviation `Type 0`;
- `DegreeData G` (M010.002, from `Degree.Fields.Definitions`), a continuous
  surjective degree homomorphism `G →ₜ* ZHatMul` (`ZHatMul` is
  `Multiplicative ZHat`);
- `ValuationData D A` (M025.012, from
  `Degree.Valuation.ValuationData.Definitions`), a henselian valuation of the
  base-field fixed module, and `ValuationData.valueGroup` (M025.013, same
  module), its value group `v(A_k)`, an additive subgroup of `ZHat`;
- `ZHat` (M008.008, from
  `GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`), the
  profinite integers;
- `ValuationData.valuationAt v K` (M025.025, from
  `Degree.Valuation.ValuationData.Normalized.Definitions`), the normalized
  valuation `v_K = (1/f_K) v ∘ N_{K|k}` on `A^{G_K}`, an additive homomorphism
  into `v.valueGroup`;
- `FiniteAbstractField G` (M010.121, from
  `Degree.Fields.FiniteAbstractField.Definitions`), a closed subgroup
  `K.field` of finite index over the base field;
- `KummerTheory.ambientFixedAddSubgroup A H` (M023.001, from
  `GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`), the
  additive subgroup `A^H` of elements of `A` fixed by `H`;
- `FiniteAbstractFieldExtension G` (M010.130, from
  `Degree.Fields.FiniteAbstractField.Extension.Definitions`), two finite
  abstract fields `E.field` (the top field `L`) and `E.base` (the base field
  `K`) with `E.below : E.field.field.toSubgroup ≤ E.base.field.toSubgroup`
  and a finite relative quotient;
- `FiniteAbstractFieldExtension.IsTotallyRamified` (M010.134) and
  `FiniteAbstractFieldExtension.degree` (M010.135, both same module): total
  ramification of the underlying finite abstract extension (the degree image
  of `G_K` is contained in that of `G_L`) and the positive degree `[L : K]`;
- `fixedFieldInclusion A K L hLK` (M028.001, from
  `Degree.PrimeElements.Definitions`), the inclusion `A^{G_K} →+ A^{G_L}`
  for `G_L ≤ G_K`.

`Rep ℤ G`, `Int.castRingHom` and the scalar multiplication `ℕ • ZHat` are
Mathlib's.

## Targets and complete telescopes

Both targets have the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`, followed by those shown. Write
`L = E.field` and `K = E.base`.

### M075.029

```lean
def abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamifiedStatement
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (x : ambientFixedAddSubgroup A E.base.field) : Prop :=
    ((v.valuationAt E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below x) :
      v.valueGroup) : ZHat) =
      (E.degree : ℕ) •
        ((v.valuationAt E.base x : v.valueGroup) : ZHat)
```

For a finite totally ramified extension `L | K` and `x ∈ A^{G_K}`, the
normalized valuation `v_L` of `x`, viewed in `A^{G_L}`, is `[L : K]` times
`v_K(x)`, both read in `ZHat`.

### M075.030

```lean
def abstractReciprocity_totallyRamified_valuation_forces_exponent_zeroStatement
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ) (hk : k < (E.degree : ℕ))
    (x : ambientFixedAddSubgroup A E.base.field)
    (hx :
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
        v.valueGroup) : ZHat) =
        Int.castRingHom ZHat (k : ℤ)) : Prop :=
    k = 0
```

For `L | K` finite and totally ramified, `k < [L : K]` and
`x ∈ A^{G_K}` whose normalized valuation in `L` is the integer `k`
(read in `ZHat`), we have `k = 0`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. Each telescope and statement
   is copied verbatim. The source proofs are omitted: this contribution
   publishes the proposition targets, and their proofs are separate work.
3. Prefix each source docstring with `Target:`, lower-case the first word
   after it and rewrap the lines; the wording is unchanged. Replace the
   source module docstring by a description of this module with a modification
   notice that names the source theorems.
4. Put `set_option linter.unusedVariables false in` before each target. The
   propositions do not mention the binders `hTot` (both targets), `hk` and
   `hx` (M075.030), and the linter would otherwise warn; the option changes
   no declaration.
5. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions`
   (M010.130, M010.134 and M010.135, which also brings M010.002 and
   M010.121),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`
   (M025.025, which also brings M025.012, M025.013, M023.001, M008.008 and
   M002.001) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions`
   (M028.001).
6. Omit the other declarations of the source file, the outer variable line
   `{D : DegreeData G} {A : Rep ℤ G}` (both targets bind `D` and `A`), and
   the unused `open CyclicCohomology` and `open CategoryTheory`. Retain
   `open KummerTheory` (for `ambientFixedAddSubgroup`), one noncomputable
   section with its comment and variable line, and the namespace.
7. No helper declaration or instance is added.

These are exact source statements as named propositions, without
published proofs. They discharge no host class-formation, cup, transfer,
Tate or reciprocity target.

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
