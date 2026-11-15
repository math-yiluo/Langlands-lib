# NYLL M014.028: the normalized degree restricted to the Frobenius closure

This file adapts one definition of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, with the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source lines (docstring, declaration) | Original name after `ClassFormation.DegreeData.` | Adapted name |
| --- | --- | --- | --- |
| M014.028 | 555, 556–564 | `frobeniusClosureDegree` | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusClosureDegree` |

## The objects

Every object used is a source definition published in the Library or a
Mathlib definition. No replacement degree datum, normalized degree, closure
or inclusion is introduced.

- `D : DegreeData G` (M010.002), `K : FiniteResidueAbstractField D`
  (M010.021), `L : ClosedSubgroup G` with
  `hLK : L.toSubgroup ≤ K.field.toSubgroup`, and the normality of
  `L.toSubgroup.subgroupOf K.field.toSubgroup`, the exact body of the source
  abbreviation `extensionSubgroup K.field L hLK` (M004.002, published as the
  abbreviation `Langlands.NYLL.CyclicCohomology.extensionSubgroup`).
- `σ : D.FrobeniusElements K L hLK` (M012.009) is a Frobenius lift, an
  element `σ.1` of the quotient
  `K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` (M012.002)
  of strictly positive natural normalized degree.
- `D.frobeniusClosure K L hLK σ` (M014.023) is the closed subgroup
  `Γ = closure ⟨σ.1⟩` of that quotient, published in the module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`.
- `D.extensionNormalizedDegreeContinuous K L hLK` (M014.016) is the
  continuous homomorphism
  `(K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) →ₜ* ZHatMul`
  whose underlying homomorphism is the factorized normalized degree
  `D.extensionNormalizedDegree K L hLK` (M012.005). It is published in the
  module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.NormalizedDegreeContinuous.Definitions`.
  `ZHatMul` (M010.001) is `Multiplicative ZHat`.
- `Langlands.NYLL.PortInternal.M014.d003 H` (M014.003) is the published
  adaptation of the source-private helper `continuousSubgroupSubtype`: for a
  subgroup `H` of a group `A` with a topology it is the continuous
  homomorphism `H →ₜ* A` with underlying homomorphism `H.subtype` and continuity
  `continuous_subtype_val`. It is published in the module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.U003.Definitions`.
- `ContinuousMonoidHom` (`→ₜ*`), `ContinuousMonoidHom.comp` and
  `ClosedSubgroup.toSubgroup` are Mathlib's.

## Telescope

The declaration has the source section's implicit `{G : Type u}` with the
source `universe u` (source lines 27 and 29), followed by `[Group G]` and
`[TopologicalSpace G]`, and then the binders below. No hypothesis is added or
removed. The normality binder is the source binder
`[hLnormal : (extensionSubgroup K.field L hLK).Normal]` with
`extensionSubgroup` expanded.

```lean
def frobeniusClosureDegree (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusClosure K L hLK σ →ₜ* ZHatMul
```

## Construction

`D.frobeniusClosureDegree K L hLK σ` (M014.028) is the restriction of the
continuous normalized degree to `Γ`: the composite
`(D.extensionNormalizedDegreeContinuous K L hLK).comp (Langlands.NYLL.PortInternal.M014.d003 (D.frobeniusClosure K L hLK σ).toSubgroup)`
of the inclusion of `Γ` into the quotient with the continuous normalized
degree. This is the source body with the private helper replaced by its
published adaptation, whose fields are those of the source helper.

## Modifications

Worker 5264 makes these modifications:

- Extract only M014.028, with the namespaces `ClassFormation` (line 19) and
  `DegreeData` (line 300), the noncomputable section (line 25), the
  universe declaration (line 27) and the variable declaration (line 29).
  Replace the module documentation by one describing this declaration and
  the modifications. The source `open CyclicCohomology` (line 21) is
  omitted: here it serves only to resolve `extensionSubgroup`, which is
  expanded below.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
- Expand `extensionSubgroup K.field L hLK` (line 559) to its exact Mathlib
  body `L.toSubgroup.subgroupOf K.field.toSubgroup`, following the
  published sibling modules. The two expressions are definitionally equal.
- Replace the source-private helper `continuousSubgroupSubtype` (line 563;
  defined at source lines 52–57) by its published adaptation
  `Langlands.NYLL.PortInternal.M014.d003` (M014.003). The published
  definition unfolds to the same fields `toMonoidHom := H.subtype` and
  `continuous_toFun := continuous_subtype_val`.
- Replace the source imports by the published modules
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`
  (M014.023 and, transitively, M010.002, M010.021, M012.002, M012.009),
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.NormalizedDegreeContinuous.Definitions`
  (M014.016) and
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.U003.Definitions`
  (M014.003).
- The declaration name, docstring, the remaining telescope, the result type
  and the remaining body are unchanged.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The source theorems M014.029 `frobeniusClosureDegree_generator` and M014.030
`frobeniusClosureDegree_range` are stated as proposition targets in the
sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.Statements`.
The other declarations of the source file are not part of this module. This
definition discharges no host class-formation, cup, transfer, Tate or
reciprocity target.

## Verification

The module and its sibling modules passed a project Lean service check on
15 November 2026 with environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), with no
errors or warnings. Compilation is separate from independent semantic
acceptance and publication.

## Attribution

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
