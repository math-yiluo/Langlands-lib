# NYLL M053.003: the Frobenius action remainder

The paired Lean file adapts the definition `frobeniusActionRemainder` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean`.
The pinned source file has SHA-256
`913562295296948d960ad31a3f03b201046ba2089b481705109cd238619c3445`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.DegreeData.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M053.003 | `frobeniusActionRemainder` | 132–133 | 134–140 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusActionRemainder` |

The enclosing source context is `universe u` (line 20),
`namespace ClassFormation` (line 22), `open KummerTheory` (line 24),
`open CyclicCohomology` (line 25), `noncomputable section` (line 27),
`open CategoryTheory` (line 29), `section actionRemainderAlgebra`
(lines 126–318), the variables `{G : Type u} [Group G] [TopologicalSpace G]`
(line 128) and `namespace DegreeData` (lines 130–316). The source imports
(lines 7–9) are the unported modules `FrobeniusDescent`, `Universal` and
`TransferOrbitClosure` of `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction`. The rest of the source file is not part of this module; the
statement of the next source theorem, M053.004, is in the sibling module
`Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder.Statements`.

The names used resolve to `Langlands.NYLL` declarations:

- `DegreeData` (M010.002) and `DegreeData.FiniteResidueAbstractField D`
  (M010.021), a closed subgroup `K.field` whose residue quotient is finite;
- `DegreeData.extensionInertiaWithin` (M012.002, from
  `Degree.FrobeniusLift.Definitions`): for `L ≤ K`, the subgroup
  `G_L ⊓ I_K` of `G_K`, normal when `G_L` is normal (instance M012.003);
- `DegreeData.extensionNormalizedDegree` (M012.005) and
  `DegreeData.FrobeniusElements` (M012.009, both from
  `Degree.FrobeniusLift.FrobeniusElements.Definitions`): the normalized
  degree `G_K ⧸ (G_L ⊓ I_K) →* ZHatMul` (where `ZHatMul` is
  `Multiplicative ZHat`), and the subtype of elements `σ` of that quotient
  whose normalized degree is `(Multiplicative.ofAdd 1) ^ n` for some natural
  `n > 0`;
- `DegreeData.frobeniusExponent` (M014.012, from
  `Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`), the chosen
  such `n` of a Frobenius element;
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`.

`ClosedSubgroup`, `Subgroup.Normal`, the quotient group and its powers and
inverses are Mathlib's.

## Definition

The definition has the binders implicit `{G : Type u}`, `[Group G]` and
`[TopologicalSpace G]`, followed by:

```lean
def frobeniusActionRemainder (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
  φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹
```

For Frobenius elements `φ` and `σ` of `G_K ⧸ (G_L ⊓ I_K)`, the element
`φⁿ σ⁻¹` of that quotient, where `n` is the Frobenius exponent of `σ`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`
   (M014.012, which also brings M010.002, M010.021, M012.002, M012.003,
   M012.005 and M012.009) and
   `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
   (M004.002).
3. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition.
4. Omit the rest of the source file, the section `actionRemainderAlgebra`
   (its variable line is kept) and the unused `open KummerTheory` and
   `open CategoryTheory`. Retain the universe, `open CyclicCohomology` (for
   `extensionSubgroup`), the noncomputable section and the namespaces.
5. The binders, docstring and body are unchanged.

No helper declaration or instance is added. This definition discharges
no host class-formation, cup, transfer, Tate or reciprocity target.

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
