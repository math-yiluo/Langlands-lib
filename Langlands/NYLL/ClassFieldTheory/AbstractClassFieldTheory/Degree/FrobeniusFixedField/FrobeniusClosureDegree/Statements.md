# NYLL M014.029 and M014.030: targets about the normalized degree on the Frobenius closure

The paired Lean file adapts the statements of two theorems from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`.
The pinned source file has SHA-256
`cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M014.029 | `frobeniusClosureDegree_generator` (`@[simp]`, line 567) | 566 | 568–577 | 578–585 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusClosureDegree_generatorStatement` |
| M014.030 | `frobeniusClosureDegree_range` | 587–589 | 590–598 | 599–684 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusClosureDegree_rangeStatement` |

The enclosing source context is `namespace ClassFormation` (line 19),
`open CyclicCohomology` (line 21), `noncomputable section` (line 25),
`universe u` (line 27), the variables at line 29 and `namespace DegreeData`
(line 300).

The names used in the statements resolve to `Langlands.NYLL` declarations:
`DegreeData.frobeniusClosureDegree` (M014.028, from the sibling module
`FrobeniusClosureDegree.Definitions` of this contribution), the
continuous homomorphism `Γ →ₜ* ZHatMul` that restricts the continuous
normalized degree to the Frobenius closure `Γ`;
`DegreeData.frobeniusClosure`, `DegreeData.frobeniusInClosure` and
`DegreeData.frobeniusExponent` (M014.023, M014.024 and M014.012, from
`Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`): `Γ` is the
closed subgroup `closure ⟨σ.1⟩` of
`K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK`,
`D.frobeniusInClosure K L hLK σ` is `σ.1` as an element of `Γ`, and
`D.frobeniusExponent K L hLK σ` is the chosen positive natural number `n`
with normalized degree of `σ.1` equal to `(Multiplicative.ofAdd (1 : ZHat)) ^ n`;
`zHatMulNat n` (M009.002, from
`GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U002.Definitions`), the
continuous additive endomorphism `x ↦ n • x` of `ZHat`;
`ZHat` (M008.008), `ZHatMul` (M010.001, `Multiplicative ZHat`),
`DegreeData.FrobeniusElements` (M012.009),
`DegreeData.extensionInertiaWithin` (M012.002),
`DegreeData.FiniteResidueAbstractField` (M010.021) and `DegreeData`
(M010.002). `ClosedSubgroup`, `Subgroup.subgroupOf`, `Subgroup.Normal`,
`ContinuousMonoidHom.toMonoidHom`, `MonoidHom.range`,
`ContinuousAddMonoidHom.toAddMonoidHom`, `AddMonoidHom.range`,
`AddSubgroup.toSubgroup` (the subgroup of `Multiplicative ZHat`
corresponding to an additive subgroup of `ZHat`), `Multiplicative.ofAdd`,
`CompactSpace` and `T2Space` are Mathlib's.

## Targets and complete telescopes

Both targets have the section binders implicit `{G : Type u}`, `[Group G]`
and `[TopologicalSpace G]`, with the single universe parameter `u`,
followed by the binders shown. The normality binder is the source binder
`[hLnormal : (extensionSubgroup K.field L hLK).Normal]` with the source
abbreviation `extensionSubgroup` (M004.002) expanded to its exact Mathlib
body. Write `Γ` for `D.frobeniusClosure K L hLK σ` and `n` for
`D.frobeniusExponent K L hLK σ`.

```lean
def frobeniusClosureDegree_generatorStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    D.frobeniusClosureDegree K L hLK σ
        (D.frobeniusInClosure K L hLK σ) =
      (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ
```

The degree on `Γ` sends the generator `σ` of `Γ` to the `n`-th power of the
multiplicative generator `Multiplicative.ofAdd 1` of `ZHatMul`.

```lean
def frobeniusClosureDegree_rangeStatement (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range =
      AddSubgroup.toSubgroup
        ((zHatMulNat (D.frobeniusExponent K L hLK σ)).toAddMonoidHom.range)
```

If `G` is in addition compact and Hausdorff, the image of the degree on `Γ`
is the subgroup `n ZHat`, written multiplicatively, that is, the range of
multiplication by `n` on `ZHat` transported to `ZHatMul`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The statements are copied
   verbatim, apart from the `extensionSubgroup` expansion in the normality
   binders. The source proofs are omitted: this contribution publishes
   proposition targets, and their proofs are separate work.
3. Omit the `@[simp]` attribute of M014.029, which cannot apply to a
   proposition-valued definition.
4. Prefix each source docstring with `Target:`, and replace the source
   module docstring by a description of this module with a modification
   notice that names the source theorems.
5. Replace the source imports by the sibling module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.Definitions`
   (which provides the M014.012, M014.023 and M014.024 names through its own
   imports) and the published module
   `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U002.Definitions`
   (M009.002).
6. Omit `open CyclicCohomology`, which in these statements served only to
   resolve the expanded `extensionSubgroup`. Retain the noncomputable
   section, the universe and variable lines and the `DegreeData` namespace.
7. Omit all other source units. No helper declaration or instance is added.

The instance binders `[CompactSpace G]` and `[T2Space G]` of M014.030 are
retained although the proposition does not use them; they are hypotheses
of the source theorem, used by its proof.

These are the exact source statements as named propositions, without
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
